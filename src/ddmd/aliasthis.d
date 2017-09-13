/**
 * Compiler implementation of the
 * $(LINK2 http://www.dlang.org, D programming language).
 *
 * Copyright:   Copyright (c) 1999-2017 by Digital Mars, All Rights Reserved
 * Authors:     $(LINK2 http://www.digitalmars.com, Walter Bright)
 * License:     $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:      $(DMDSRC _aliasthis.d)
 */

module ddmd.aliasthis;

import core.stdc.stdio;
import ddmd.aggregate;
import ddmd.declaration;
import ddmd.dscope;
import ddmd.dsymbol;
import ddmd.errors;
import ddmd.expression;
import ddmd.globals;
import ddmd.identifier;
import ddmd.mtype;
import ddmd.opover;
import ddmd.tokens;
import ddmd.visitor;

/***********************************************************
 * alias ident this;
 */
extern (C++) final class AliasThis : Dsymbol
{
    Identifier ident;

    extern (D) this(Loc loc, Identifier ident)
    {
        super(null);    // it's anonymous (no identifier)
        this.loc = loc;
        this.ident = ident;
    }

    override Dsymbol syntaxCopy(Dsymbol s)
    {
        assert(!s);
        return new AliasThis(loc, ident);
    }

    override void addMember(Scope* sc, ScopeDsymbol sds)
    {
        if (addMemberState == SemState.Done)
            return;

        void defer() { addMemberState = SemState.Defer; }

        if (addMemberState == SemState.Init)
            super.addMember(sc, sds);

        Dsymbol p = sc.parent.pastMixin();
        AggregateDeclaration ad = p.isAggregateDeclaration();
        if (!ad)
        {
            .error(loc, "alias this can only be a member of aggregate, not %s `%s`", p.kind(), p.toChars());
            return;
        }

        assert(ad.members);
        Dsymbol s = ad.search(loc, ident);
        if (!s)
        {
            if (ad.membersState == SemState.Defer)
                return defer();

            s = sc.search(loc, ident, null);
            if (s)
                .error(loc, "`%s` is not a member of `%s`", s.toChars(), ad.toChars());
            else
                .error(loc, "undefined identifier `%s`", ident.toChars());
            aliasState = SemState.Done;
            return;
        }
        if (ad.aliasthis && s != ad.aliasthis)
        {
            .error(loc, "there can be only one alias this");
            return;
        }
        ad.aliasthis = s.isAliasDeclaration() ? s.toAlias() : s;
    }

    override void semantic()
    {
        if (semanticState == SemState.Done)
            return;
        semanticState = SemState.In;

        assert(addMemberState == SemState.Done);

        Dsymbol p = _scope.parent.pastMixin();
        AggregateDeclaration ad = p.isAggregateDeclaration();

        /* disable the alias this conversion so the implicit conversion check
         * doesn't use it.
         */
        Dsymbol sx = ad.aliasthis;
        ad.aliasthis = null;
        Declaration d = sx.isDeclaration();
        if (d && !d.isTupleDeclaration())
        {
            Type t = d.type;
            assert(t);
            if (ad.type.implicitConvTo(t) > MATCHnomatch)
            {
                .error(loc, "alias this is not reachable as `%s` already converts to `%s`", ad.toChars(), t.toChars());
            }
        }
        ad.aliasthis = sx;

        semanticState = SemState.Done;
    }

    override const(char)* kind() const
    {
        return "alias this";
    }

    AliasThis isAliasThis()
    {
        return this;
    }

    override void accept(Visitor v)
    {
        v.visit(this);
    }
}

extern (C++) Expression resolveAliasThis(Scope* sc, Expression e, bool gag = false)
{
    AggregateDeclaration ad = isAggregate(e.type);
    if (ad && ad.aliasthis)
    {
        uint olderrors = gag ? global.startGagging() : 0;
        Loc loc = e.loc;
        Type tthis = (e.op == TOKtype ? e.type : null);
        e = new DotIdExp(loc, e, ad.aliasthis.ident);
        e = e.semantic(sc);
        if (tthis && ad.aliasthis.needThis())
        {
            if (e.op == TOKvar)
            {
                if (auto fd = (cast(VarExp)e).var.isFuncDeclaration())
                {
                    // https://issues.dlang.org/show_bug.cgi?id=13009
                    // Support better match for the overloaded alias this.
                    bool hasOverloads;
                    if (auto f = fd.overloadModMatch(loc, tthis, hasOverloads))
                    {
                        if (!hasOverloads)
                            fd = f;     // use exact match
                        e = new VarExp(loc, fd, hasOverloads);
                        e.type = f.type;
                        e = new CallExp(loc, e);
                        goto L1;
                    }
                }
            }
            /* non-@property function is not called inside typeof(),
             * so resolve it ahead.
             */
            {
                int save = sc.intypeof;
                sc.intypeof = 1; // bypass "need this" error check
                e = resolveProperties(sc, e);
                sc.intypeof = save;
            }
        L1:
            e = new TypeExp(loc, new TypeTypeof(loc, e));
            e = e.semantic(sc);
        }
        e = resolveProperties(sc, e);
        if (gag && global.endGagging(olderrors))
            e = null;
    }
    return e;
}
