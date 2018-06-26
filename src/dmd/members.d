/**
 * Compiler implementation of the
 * $(LINK2 http://www.dlang.org, D programming language).
 *
 * Copyright:   Copyright (C) 1999-2018 by The D Language Foundation, All Rights Reserved
 * Authors:     $(LINK2 http://www.digitalmars.com, Walter Bright)
 * License:     $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:      $(LINK2 https://github.com/dlang/dmd/blob/master/src/dmd/semantic2.d, _semantic2.d)
 * Documentation:  https://dlang.org/phobos/dmd_semantic2.html
 * Coverage:    https://codecov.io/gh/dlang/dmd/src/master/src/dmd/semantic2.d
 */

module dmd.members;

import core.stdc.stdio;
import core.stdc.string;

import dmd.aggregate;
import dmd.aliasthis;
import dmd.arraytypes;
import dmd.astcodegen;
import dmd.attrib;
import dmd.blockexit;
import dmd.clone;
import dmd.dcast;
import dmd.dclass;
import dmd.declaration;
import dmd.denum;
import dmd.dimport;
import dmd.dinterpret;
import dmd.dmodule;
import dmd.dscope;
import dmd.dstruct;
import dmd.dsymbol;
import dmd.dsymbolsem;
import dmd.dtemplate;
import dmd.dversion;
import dmd.errors;
import dmd.escape;
import dmd.expression;
import dmd.expressionsem;
import dmd.func;
import dmd.globals;
import dmd.id;
import dmd.identifier;
import dmd.init;
import dmd.initsem;
import dmd.hdrgen;
import dmd.mars;
import dmd.mtype;
import dmd.nogc;
import dmd.nspace;
import dmd.objc;
import dmd.opover;
import dmd.parse;
import dmd.root.filename;
import dmd.root.outbuffer;
import dmd.root.rmem;
import dmd.root.rootobject;
import dmd.sideeffect;
import dmd.statementsem;
import dmd.staticassert;
import dmd.tokens;
import dmd.utf;
import dmd.utils;
import dmd.statement;
import dmd.target;
import dmd.templateparamsem;
import dmd.typesem;
import dmd.visitor;

enum LOG = false;


/*************************************
 * Fills the symtab of a ScopeDsymbol
 */
extern(C++) void determineSymtab(Dsymbol dsym, Scope* sc)
{
    scope v = new DetermineSymtabVisitor(sc);
    dsym.accept(v);
}

private extern(C++) final class DetermineSymtabVisitor : Visitor
{
    alias visit = Visitor.visit;

    Scope* sc;
    this(Scope* sc)
    {
        this.sc = sc;
    }

    override void visit(Dsymbol) {}

    override void visit(ScopeDsymbol sds)
    {
        with (sds)
        {
            switch (symtabState)
            {
                default:
                    return;

                case SemState.Defer:
                case SemState.Init:
                    nextMember = 0;
                    numDeferredMembers = 0;
                    goto case;

                case SemState.In:
                {
                    symtabState = SemState.In;
                    if (!members) // if opaque declaration
                    {
                        symtabState = SemState.Done;
                        return;
                    }

                    if (!symtab)
                        symtab = new DsymbolTable();

                    auto sc2 = newScope(sc);
                    scope(exit) while (sc2 != sc)
                        sc2 = sc2.pop();

                    ++membersNest;
                    while (nextMember < members.dim)
                    {
                        auto s = (*members)[nextMember++];
                        if (s.addMemberState == SemState.Done)
                            continue; // FIXME this is temporary to avoid extra setScope calls
                        s.addMember(sc2, sc2.scopesym);
                        s.setScope(sc2); // FIXME: should go into addMember
                        if (s.addMemberState == SemState.Defer)
                            numDeferredMembers++;
                    }
                    --membersNest;

                    if (membersNest)
                        return;

                    if (numDeferredMembers < lastDeferredMembers)
                        Module.dprogress++;

                    if (!numDeferredMembers)
                        symtabState = SemState.Done;
                    else
                    {
                        lastDeferredMembers = numDeferredMembers;
                        symtabState = SemState.Defer;
                    }
                }
            }
        }
    }

    override void visit(Module m)
    {
        with (m)
        {
            // Add import of "object", even for the "object" module.
            // If it isn't there, some compiler rewrites, like
            //    classinst == classinst -> .object.opEquals(classinst, classinst)
            // would fail inside object.d.
            if (members.dim == 0 || (*members)[0].ident != Id.object)
            {
                auto im = new Import(Loc.initial, null, Id.object, null, 0);
                members.shift(im);
            }

            super.visit(m);
        }
    }

    override void visit(ClassDeclaration cldec)
    {
        with (cldec)
        {
            determineBaseClasses(cldec, sc, _scope);
            super.visit(cldec);
        }
    }

    override void visit(TemplateDeclaration tempdecl)
    {
        with (tempdecl)
        {
            symtabState = SemState.Done;
        }
    }

    override void visit(TemplateInstance tempinst)
    {
        with (tempinst)
        {
            if (symtabState == SemState.Done)
                return;

            void mirrorInst()
            {
                inst.determineSymtab(sc);
                symtabState = inst.symtabState;
            }

            if (inst && tempinst != inst)
                return mirrorInst();

            if (symtabState == SemState.Init)
            {
                if (!sc)
                    return; // FIXME? this is for deduceFunctionTemplateMatch where search() looks for parameters but the tempinst mustn't get semantic'd (parameters are already added)

                // Get the enclosing template instance from the scope tinst
                tinst = sc.tinst;

                // Get the instantiating module from the scope minst
                minst = sc.minst;
                // https://issues.dlang.org/show_bug.cgi?id=10920
                // If the enclosing function is non-root symbol,
                // this instance should be speculative.
                if (!tinst && sc.func && sc.func.inNonRoot())
                {
                    minst = null;
                }

                gagged = (global.gag > 0);

                /* Find template declaration first,
                * then run semantic on each argument (place results in tiargs[]),
                * last find most specialized template from overload list/set.
                */
                if (!tempinst.findTempDecl(sc, null) || !tempinst.semanticTiargs(sc) || !tempinst.findBestMatch(sc, fargs))
                {
                Lerror:
                    if (tempinst.gagged)
                    {
                        // https://issues.dlang.org/show_bug.cgi?id=13220
                        // Roll back status for later semantic re-running
                        tempinst.semanticRun = PASS.init;
                    }
                    else
                        tempinst.inst = tempinst;
                    tempinst.errors = true;
                    return;
                }
                TemplateDeclaration tempdecl = tempinst.tempdecl.isTemplateDeclaration();
                assert(tempdecl);

                // If tempdecl is a mixin, disallow it
                if (tempdecl.ismixin)
                {
                    tempinst.error("mixin templates are not regular templates");
                    goto Lerror;
                }

                tempinst.hasNestedArgs(tempinst.tiargs, tempdecl.isstatic);
                if (tempinst.errors)
                    goto Lerror;

                /* See if there is an existing TemplateInstantiation that already
                * implements the typeargs. If so, just refer to that one instead.
                */
                tempinst.inst = tempdecl.findExistingInstance(tempinst, fargs);
                /+TemplateInstance +/errinst = null;
                if (!tempinst.inst)
                {
                    // So, we need to implement 'this' instance.
                }
                else if (tempinst.inst.gagged && !tempinst.gagged && tempinst.inst.errors)
                {
                    // If the first instantiation had failed, re-run semantic,
                    // so that error messages are shown.
                    errinst = tempinst.inst;
                }
                else
                {
                    // It's a match
                    tempinst.parent = tempinst.inst.parent;
                    tempinst.errors = tempinst.inst.errors;

                    // If both this and the previous instantiation were gagged,
                    // use the number of errors that happened last time.
                    global.errors += tempinst.errors;
                    global.gaggedErrors += tempinst.errors;

                    // If the first instantiation was gagged, but this is not:
                    if (tempinst.inst.gagged)
                    {
                        // It had succeeded, mark it is a non-gagged instantiation,
                        // and reuse it.
                        tempinst.inst.gagged = tempinst.gagged;
                    }

                    tempinst.tnext = tempinst.inst.tnext;
                    tempinst.inst.tnext = tempinst;

                    /* A module can have explicit template instance and its alias
                    * in module scope (e,g, `alias Base64 = Base64Impl!('+', '/');`).
                    * If the first instantiation 'inst' had happened in non-root module,
                    * compiler can assume that its instantiated code would be included
                    * in the separately compiled obj/lib file (e.g. phobos.lib).
                    *
                    * However, if 'this' second instantiation happened in root module,
                    * compiler might need to invoke its codegen
                    * (https://issues.dlang.org/show_bug.cgi?id=2500 & https://issues.dlang.org/show_bug.cgi?id=2644).
                    * But whole import graph is not determined until all semantic pass finished,
                    * so 'inst' should conservatively finish the semantic3 pass for the codegen.
                    */
                    if (tempinst.minst && tempinst.minst.isRoot() && !(tempinst.inst.minst && tempinst.inst.minst.isRoot()))
                    {
                        /* Swap the position of 'inst' and 'this' in the instantiation graph.
                        * Then, the primary instance `inst` will be changed to a root instance.
                        *
                        * Before:
                        *  non-root -> A!() -> B!()[inst] -> C!()
                        *                      |
                        *  root     -> D!() -> B!()[this]
                        *
                        * After:
                        *  non-root -> A!() -> B!()[this]
                        *                      |
                        *  root     -> D!() -> B!()[inst] -> C!()
                        */
                        Module mi = tempinst.minst;
                        TemplateInstance ti = tempinst.tinst;
                        tempinst.minst = tempinst.inst.minst;
                        tempinst.tinst = tempinst.inst.tinst;
                        tempinst.inst.minst = mi;
                        tempinst.inst.tinst = ti;

                        if (tempinst.minst) // if inst was not speculative
                        {
                            /* Add 'inst' once again to the root module members[], then the
                            * instance members will get codegen chances.
                            */
                            tempinst.inst.appendToModuleMember();
                        }
                    }
                    static if (LOG)
                    {
                        printf("\tit's a match with instance %p, %d\n", tempinst.inst, tempinst.inst.semanticRun);
                    }
                    return mirrorInst();
                }
                static if (LOG)
                {
                    printf("\timplement template instance %s '%s'\n", tempdecl.parent.toChars(), tempinst.toChars());
                    printf("\ttempdecl %s\n", tempdecl.toChars());
                }
                uint errorsave = global.errors;

                tempinst.inst = tempinst;
                tempinst.parent = tempinst.enclosing ? tempinst.enclosing : tempdecl.parent;
                //printf("parent = '%s'\n", parent.kind());

                /+TemplateInstance +/tempdecl_instance_idx = tempdecl.addInstance(tempinst);

                //getIdent();

                // Store the place we added it to in target_symbol_list(_idx) so we can
                // remove it later if we encounter an error.
                /+Dsymbols* +/target_symbol_list = tempinst.appendToModuleMember();
                /+size_t +/target_symbol_list_idx = target_symbol_list ? target_symbol_list.dim - 1 : 0;

                // Copy the syntax trees from the TemplateDeclaration
                tempinst.members = Dsymbol.arraySyntaxCopy(tempdecl.members);

                // resolve TemplateThisParameter
                for (size_t i = 0; i < tempdecl.parameters.dim; i++)
                {
                    if ((*tempdecl.parameters)[i].isTemplateThisParameter() is null)
                        continue;
                    Type t = isType((*tempinst.tiargs)[i]);
                    assert(t);
                    if (StorageClass stc = ModToStc(t.mod))
                    {
                        //printf("t = %s, stc = x%llx\n", t.toChars(), stc);
                        auto s = new Dsymbols();
                        s.push(new StorageClassDeclaration(stc, tempinst.members));
                        tempinst.members = s;
                    }
                    break;
                }
            }

            sc = tempdecl._scope; // FIXME: this isn't pretty.. but also a special case?
            super.visit(tempinst);

            if (symtabState != SemState.Done)
                return;

            static if (LOG)
            {
                printf("adding members done\n");
            }

            TemplateDeclaration tempdecl = tempinst.tempdecl.isTemplateDeclaration();

            /* See if there is only one member of template instance, and that
            * member has the same name as the template instance.
            * If so, this template instance becomes an alias for that member.
            */
            //printf("members.dim = %d\n", members.dim);
            if (tempinst.members.dim)
            {
                Dsymbol s;
                if (Dsymbol.oneMembers(tempinst.members, &s, tempdecl.ident) && s)
                {
                    //printf("tempdecl.ident = %s, s = '%s'\n", tempdecl.ident.toChars(), s.kind(), s.toPrettyChars());
                    //printf("setting aliasdecl\n");
                    tempinst.aliasdecl = s;
                }
            }
        }
    }
}
