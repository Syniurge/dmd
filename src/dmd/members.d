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
                        s.addMember(sc2, sc2.scopesym);
                        s.setScope(sc2); // FIXME: should go into addMember
                        if (s.addMemberState == SemState.Defer)
                            numDeferredMembers++;
                    }
                    --membersNest;

                    if (membersNest)
                        return;

                    if (!numDeferredMembers)
                        symtabState = SemState.Done;
                    else
                    {
                        if (numDeferredMembers < lastDeferredMembers)
                            Module.dprogress++;
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
            symtabState = SemState.Done;
        }
    }
}
