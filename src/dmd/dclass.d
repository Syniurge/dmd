/**
 * Compiler implementation of the
 * $(LINK2 http://www.dlang.org, D programming language).
 *
 * Copyright:   Copyright (C) 1999-2018 by The D Language Foundation, All Rights Reserved
 * Authors:     $(LINK2 http://www.digitalmars.com, Walter Bright)
 * License:     $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:      $(LINK2 https://github.com/dlang/dmd/blob/master/src/dmd/dclass.d, _dclass.d)
 * Documentation:  https://dlang.org/phobos/dmd_dclass.html
 * Coverage:    https://codecov.io/gh/dlang/dmd/src/master/src/dmd/dclass.d
 */

module dmd.dclass;

import core.stdc.stdio;
import core.stdc.string;

import dmd.aggregate;
import dmd.arraytypes;
import dmd.gluelayer;
import dmd.declaration;
import dmd.dscope;
import dmd.dsymbol;
import dmd.dsymbolsem;
import dmd.func;
import dmd.globals;
import dmd.id;
import dmd.identifier;
import dmd.members;
import dmd.mtype;
import dmd.objc;
import dmd.root.rmem;
import dmd.target;
import dmd.visitor;

enum Abstract : int
{
    fwdref = 0,      // whether an abstract class is not yet computed
    yes,             // is abstract class
    no,              // is not abstract class
}

/***********************************************************
 */
struct BaseClass
{
    Type type;          // (before semantic processing)

    ClassDeclaration sym;
    uint offset;        // 'this' pointer offset

    // for interfaces: Array of FuncDeclaration's making up the vtbl[]
    FuncDeclarations vtbl;

    // if BaseClass is an interface, these
    // are a copy of the InterfaceDeclaration.interfaces
    BaseClass[] baseInterfaces;

    extern (D) this(Type type)
    {
        //printf("BaseClass(this = %p, '%s')\n", this, type.toChars());
        this.type = type;
    }

    /****************************************
     * Fill in vtbl[] for base class based on member functions of class cd.
     * Input:
     *      vtbl            if !=NULL, fill it in
     *      newinstance     !=0 means all entries must be filled in by members
     *                      of cd, not members of any base classes of cd.
     * Returns:
     *      true if any entries were filled in by members of cd (not exclusively
     *      by base classes)
     */
    extern (C++) bool fillVtbl(ClassDeclaration cd, FuncDeclarations* vtbl, int newinstance)
    {
        bool result = false;

        //printf("BaseClass.fillVtbl(this='%s', cd='%s')\n", sym.toChars(), cd.toChars());
        if (vtbl)
            vtbl.setDim(sym.vtbl.dim);

        // first entry is ClassInfo reference
        for (size_t j = sym.vtblOffset(); j < sym.vtbl.dim; j++)
        {
            FuncDeclaration ifd = sym.vtbl[j].isFuncDeclaration();
            FuncDeclaration fd;
            TypeFunction tf;

            //printf("        vtbl[%d] is '%s'\n", j, ifd ? ifd.toChars() : "null");
            assert(ifd);

            // Find corresponding function in this class
            tf = ifd.type.toTypeFunction();
            fd = cd.findFunc(ifd.ident, tf);
            if (fd && !fd.isAbstract())
            {
                //printf("            found\n");
                // Check that calling conventions match
                if (fd.linkage != ifd.linkage)
                    fd.error("linkage doesn't match interface function");

                // Check that it is current
                //printf("newinstance = %d fd.toParent() = %s ifd.toParent() = %s\n",
                    //newinstance, fd.toParent().toChars(), ifd.toParent().toChars());
                if (newinstance && fd.toParent() != cd && ifd.toParent() == sym)
                    cd.error("interface function `%s` is not implemented", ifd.toFullSignature());

                if (fd.toParent() == cd)
                    result = true;
            }
            else
            {
                //printf("            not found %p\n", fd);
                // BUG: should mark this class as abstract?
                if (!cd.isAbstract())
                    cd.error("interface function `%s` is not implemented", ifd.toFullSignature());

                fd = null;
            }
            if (vtbl)
                (*vtbl)[j] = fd;
        }
        return result;
    }

    extern (C++) void copyBaseInterfaces(BaseClasses* vtblInterfaces)
    {
        //printf("+copyBaseInterfaces(), %s\n", sym.toChars());
        //    if (baseInterfaces.length)
        //      return;
        auto bc = cast(BaseClass*)mem.xcalloc(sym.interfaces.length, BaseClass.sizeof);
        baseInterfaces = bc[0 .. sym.interfaces.length];
        //printf("%s.copyBaseInterfaces()\n", sym.toChars());
        for (size_t i = 0; i < baseInterfaces.length; i++)
        {
            BaseClass* b = &baseInterfaces[i];
            BaseClass* b2 = sym.interfaces[i];

            assert(b2.vtbl.dim == 0); // should not be filled yet
            memcpy(b, b2, BaseClass.sizeof);

            if (i) // single inheritance is i==0
                vtblInterfaces.push(b); // only need for M.I.
            b.copyBaseInterfaces(vtblInterfaces);
        }
        //printf("-copyBaseInterfaces\n");
    }
}

struct ClassFlags
{
    alias Type = uint;

    enum Enum : int
    {
        isCOMclass = 0x1,
        noPointers = 0x2,
        hasOffTi = 0x4,
        hasCtor = 0x8,
        hasGetMembers = 0x10,
        hasTypeInfo = 0x20,
        isAbstract = 0x40,
        isCPPclass = 0x80,
        hasDtor = 0x100,
    }

    alias isCOMclass = Enum.isCOMclass;
    alias noPointers = Enum.noPointers;
    alias hasOffTi = Enum.hasOffTi;
    alias hasCtor = Enum.hasCtor;
    alias hasGetMembers = Enum.hasGetMembers;
    alias hasTypeInfo = Enum.hasTypeInfo;
    alias isAbstract = Enum.isAbstract;
    alias isCPPclass = Enum.isCPPclass;
    alias hasDtor = Enum.hasDtor;
}

/**
 * The ClassKind enum is used in ClassDeclaration AST nodes
 * to specify the linkage type of the class or if it is an
 * anonymous class. If the class is anonymous it is also
 * considered to be a D class.
 */
enum ClassKind : int
{
    /// the class is a d(efault) class
    d,
    /// the class is a C++ interface
    cpp,
    /// the class is an Objective-C class/interface
    objc,
}

/***********************************************************
 */
extern (C++) class ClassDeclaration : AggregateDeclaration
{
    extern (C++) __gshared
    {
        // Names found by reading object.d in druntime
        ClassDeclaration object;
        ClassDeclaration throwable;
        ClassDeclaration exception;
        ClassDeclaration errorException;
        ClassDeclaration cpp_type_info_ptr;   // Object.__cpp_type_info_ptr
    }

    ClassDeclaration baseClass; // NULL only if this is Object
    FuncDeclaration staticCtor;
    FuncDeclaration staticDtor;
    Dsymbols vtbl;              // Array of FuncDeclaration's making up the vtbl[]
    Dsymbols vtblFinal;         // More FuncDeclaration's that aren't in vtbl[]

    // Array of BaseClass's; first is super, rest are Interface's
    BaseClasses* baseclasses;

    /* Slice of baseclasses[] that does not include baseClass
     */
    BaseClass*[] interfaces;

    // array of base interfaces that have their own vtbl[]
    BaseClasses* vtblInterfaces;

    // the ClassInfo object for this ClassDeclaration
    TypeInfoClassDeclaration vclassinfo;

    // true if this is a COM class
    bool com;

    /// true if this is a scope class
    bool stack;

    /// specifies whether this is a D, C++, Objective-C or anonymous class/interface
    ClassKind classKind;

    /// to prevent recursive attempts
    private bool inuse;

    /// true if this class has an identifier, but was originally declared anonymous
    /// used in support of https://issues.dlang.org/show_bug.cgi?id=17371
    private bool isActuallyAnonymous;

    Abstract isabstract;

    /// set the progress of base classes resolving
    Baseok baseok;

    /**
     * Data for a class declaration that is needed for the Objective-C
     * integration.
     */
    ObjcClassDeclaration objc;

    Symbol* cpp_type_info_ptr_sym;      // cached instance of class Id.cpp_type_info_ptr

    final extern (D) this(Loc loc, Identifier id, BaseClasses* baseclasses, Dsymbols* members, bool inObject)
    {
        if (!id)
        {
            id = Identifier.generateId("__anonclass");
            isActuallyAnonymous = true;
        }
        assert(id);

        super(loc, id);

        static __gshared const(char)* msg = "only object.d can define this reserved class name";

        if (baseclasses)
        {
            // Actually, this is a transfer
            this.baseclasses = baseclasses;
        }
        else
            this.baseclasses = new BaseClasses();

        this.members = members;

        //printf("ClassDeclaration(%s), dim = %d\n", id.toChars(), this.baseclasses.dim);

        // For forward references
        type = new TypeClass(this);

        if (id)
        {
            // Look for special class names
            if (id == Id.__sizeof || id == Id.__xalignof || id == Id._mangleof)
                error("illegal class name");

            // BUG: What if this is the wrong TypeInfo, i.e. it is nested?
            if (id.toChars()[0] == 'T')
            {
                if (id == Id.TypeInfo)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.dtypeinfo = this;
                }
                if (id == Id.TypeInfo_Class)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfoclass = this;
                }
                if (id == Id.TypeInfo_Interface)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfointerface = this;
                }
                if (id == Id.TypeInfo_Struct)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfostruct = this;
                }
                if (id == Id.TypeInfo_Pointer)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfopointer = this;
                }
                if (id == Id.TypeInfo_Array)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfoarray = this;
                }
                if (id == Id.TypeInfo_StaticArray)
                {
                    //if (!inObject)
                    //    Type.typeinfostaticarray.error("%s", msg);
                    Type.typeinfostaticarray = this;
                }
                if (id == Id.TypeInfo_AssociativeArray)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfoassociativearray = this;
                }
                if (id == Id.TypeInfo_Enum)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfoenum = this;
                }
                if (id == Id.TypeInfo_Function)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfofunction = this;
                }
                if (id == Id.TypeInfo_Delegate)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfodelegate = this;
                }
                if (id == Id.TypeInfo_Tuple)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfotypelist = this;
                }
                if (id == Id.TypeInfo_Const)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfoconst = this;
                }
                if (id == Id.TypeInfo_Invariant)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfoinvariant = this;
                }
                if (id == Id.TypeInfo_Shared)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfoshared = this;
                }
                if (id == Id.TypeInfo_Wild)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfowild = this;
                }
                if (id == Id.TypeInfo_Vector)
                {
                    if (!inObject)
                        error("%s", msg);
                    Type.typeinfovector = this;
                }
            }

            if (id == Id.Object)
            {
                if (!inObject)
                    error("%s", msg);
                object = this;
            }

            if (id == Id.Throwable)
            {
                if (!inObject)
                    error("%s", msg);
                throwable = this;
            }
            if (id == Id.Exception)
            {
                if (!inObject)
                    error("%s", msg);
                exception = this;
            }
            if (id == Id.Error)
            {
                if (!inObject)
                    error("%s", msg);
                errorException = this;
            }
            if (id == Id.cpp_type_info_ptr)
            {
                if (!inObject)
                    error("%s", msg);
                cpp_type_info_ptr = this;
            }
        }
        baseok = Baseok.none;
    }

    static ClassDeclaration create(Loc loc, Identifier id, BaseClasses* baseclasses, Dsymbols* members, bool inObject)
    {
        return new ClassDeclaration(loc, id, baseclasses, members, inObject);
    }

    override Dsymbol syntaxCopy(Dsymbol s)
    {
        //printf("ClassDeclaration.syntaxCopy('%s')\n", toChars());
        ClassDeclaration cd =
            s ? cast(ClassDeclaration)s
              : new ClassDeclaration(loc, ident, null, null, false);

        cd.storage_class |= storage_class;

        cd.baseclasses.setDim(this.baseclasses.dim);
        for (size_t i = 0; i < cd.baseclasses.dim; i++)
        {
            BaseClass* b = (*this.baseclasses)[i];
            auto b2 = new BaseClass(b.type.syntaxCopy());
            (*cd.baseclasses)[i] = b2;
        }

        return ScopeDsymbol.syntaxCopy(cd);
    }

    override Scope* newScope(Scope* sc)
    {
        auto sc2 = super.newScope(sc);
        if (isCOMclass())
        {
            /* This enables us to use COM objects under Linux and
             * work with things like XPCOM
             */
            sc2.linkage = Target.systemLinkage();
        }
        return sc2;
    }

    /*********************************************
     * Determine if 'this' is a base class of cd.
     * This is used to detect circular inheritance only.
     */
    final bool isBaseOf2(ClassDeclaration cd)
    {
        if (!cd)
            return false;
        //printf("ClassDeclaration.isBaseOf2(this = '%s', cd = '%s')\n", toChars(), cd.toChars());
        for (size_t i = 0; i < cd.baseclasses.dim; i++)
        {
            BaseClass* b = (*cd.baseclasses)[i];
            if (b.sym == this || isBaseOf2(b.sym))
                return true;
        }
        return false;
    }

    enum OFFSET_RUNTIME = 0x76543210;
    enum OFFSET_FWDREF = 0x76543211;

    /*******************************************
     * Determine if 'this' is a base class of cd.
     */
    bool isBaseOf(ClassDeclaration cd, int* poffset)
    {
        //printf("ClassDeclaration.isBaseOf(this = '%s', cd = '%s')\n", toChars(), cd.toChars());
        if (poffset)
            *poffset = 0;
        while (cd)
        {
            /* cd.baseClass might not be set if cd is forward referenced.
             */
            if (!cd.baseClass && cd.semanticRun < PASS.semanticdone && !cd.isInterfaceDeclaration())
            {
                cd.dsymbolSemantic(null);
                if (!cd.baseClass && cd.semanticRun < PASS.semanticdone)
                    cd.error("base class is forward referenced by `%s`", toChars());
            }

            if (this == cd.baseClass)
                return true;

            cd = cd.baseClass;
        }
        return false;
    }

    /*********************************************
     * Determine if 'this' has complete base class information.
     * This is used to detect forward references in covariant overloads.
     */
    final bool isBaseInfoComplete() const
    {
        return baseok >= Baseok.done;
    }

    override final Dsymbol search(const ref Loc loc, Identifier ident, int flags = SearchLocalsOnly)
    {
        //printf("%s.ClassDeclaration.search('%s', flags=x%x)\n", toChars(), ident.toChars(), flags);
        //if (_scope) printf("%s baseok = %d\n", toChars(), baseok);
        if (_scope && baseok < Baseok.done)
        {
            if (!inuse)
            {
                // must semantic on base class/interfaces
                inuse = true;
                determineSymtab(this, _scope); // FWDREF FIXME
                inuse = false;
            }
        }

        if (!members || !symtab) // opaque or addMember is not yet done
        {
            error("is forward referenced when looking for `%s`", ident.toChars());
            //*(char*)0=0;
            return null;
        }

        auto s = ScopeDsymbol.search(loc, ident, flags);

        // don't search imports of base classes
        if (flags & SearchImportsOnly)
            return s;

        if (!s)
        {
            // Search bases classes in depth-first, left to right order
            for (size_t i = 0; i < baseclasses.dim; i++)
            {
                BaseClass* b = (*baseclasses)[i];
                if (b.sym)
                {
                    if (!b.sym.symtab)
                        error("base `%s` is forward referenced", b.sym.ident.toChars());
                    else
                    {
                        import dmd.access : symbolIsVisible;

                        s = b.sym.search(loc, ident, flags);
                        if (!s)
                            continue;
                        else if (s == this) // happens if s is nested in this and derives from this
                            s = null;
                        else if (!(flags & IgnoreSymbolVisibility) && !(s.prot().kind == Prot.Kind.protected_) && !symbolIsVisible(this, s))
                            s = null;
                        else
                            break;
                    }
                }
            }
        }
        return s;
    }

    /************************************
     * Search base classes in depth-first, left-to-right order for
     * a class or interface named 'ident'.
     * Stops at first found. Does not look for additional matches.
     * Params:
     *  ident = identifier to search for
     * Returns:
     *  ClassDeclaration if found, null if not
     */
    final ClassDeclaration searchBase(Identifier ident)
    {
        foreach (b; *baseclasses)
        {
            auto cdb = b.type.isClassHandle();
            if (!cdb) // https://issues.dlang.org/show_bug.cgi?id=10616
                return null;
            if (cdb.ident.equals(ident))
                return cdb;
            auto result = cdb.searchBase(ident);
            if (result)
                return result;
        }
        return null;
    }

    final override void finalizeSize()
    {
        assert(sizeok != Sizeok.done);

        // Set the offsets of the fields and determine the size of the class
        if (baseClass)
        {
            assert(baseClass.sizeok == Sizeok.done);

            alignsize = baseClass.alignsize;
            structsize = baseClass.structsize;
            if (classKind == ClassKind.cpp && global.params.isWindows)
                structsize = (structsize + alignsize - 1) & ~(alignsize - 1);
        }
        else if (isInterfaceDeclaration())
        {
            if (interfaces.length == 0)
            {
                alignsize = Target.ptrsize;
                structsize = Target.ptrsize;      // allow room for __vptr
            }
        }
        else
        {
            alignsize = Target.ptrsize;
            structsize = Target.ptrsize;      // allow room for __vptr
            if (classKind != ClassKind.cpp)
                structsize += Target.ptrsize; // allow room for __monitor
        }

        //printf("finalizeSize() %s, sizeok = %d\n", toChars(), sizeok);
        size_t bi = 0;                  // index into vtblInterfaces[]

        /****
         * Runs through the inheritance graph to set the BaseClass.offset fields.
         * Recursive in order to account for the size of the interface classes, if they are
         * more than just interfaces.
         * Params:
         *      cd = interface to look at
         *      baseOffset = offset of where cd will be placed
         * Returns:
         *      subset of instantiated size used by cd for interfaces
         */
        uint membersPlace(ClassDeclaration cd, uint baseOffset)
        {
            //printf("    membersPlace(%s, %d)\n", cd.toChars(), baseOffset);
            uint offset = baseOffset;

            foreach (BaseClass* b; cd.interfaces)
            {
                if (b.sym.sizeok != Sizeok.done)
                    b.sym.finalizeSize();
                assert(b.sym.sizeok == Sizeok.done);

                if (!b.sym.alignsize)
                    b.sym.alignsize = Target.ptrsize;
                alignmember(b.sym.alignsize, b.sym.alignsize, &offset);
                assert(bi < vtblInterfaces.dim);

                BaseClass* bv = (*vtblInterfaces)[bi];
                if (b.sym.interfaces.length == 0)
                {
                    //printf("\tvtblInterfaces[%d] b=%p b.sym = %s, offset = %d\n", bi, bv, bv.sym.toChars(), offset);
                    bv.offset = offset;
                    ++bi;
                    // All the base interfaces down the left side share the same offset
                    for (BaseClass* b2 = bv; b2.baseInterfaces.length; )
                    {
                        b2 = &b2.baseInterfaces[0];
                        b2.offset = offset;
                        //printf("\tvtblInterfaces[%d] b=%p   sym = %s, offset = %d\n", bi, b2, b2.sym.toChars(), b2.offset);
                    }
                }
                membersPlace(b.sym, offset);
                //printf(" %s size = %d\n", b.sym.toChars(), b.sym.structsize);
                offset += b.sym.structsize;
                if (alignsize < b.sym.alignsize)
                    alignsize = b.sym.alignsize;
            }
            return offset - baseOffset;
        }

        structsize += membersPlace(this, structsize);

        if (isInterfaceDeclaration())
        {
            sizeok = Sizeok.done;
            return;
        }

        // FIXME: Currently setFieldOffset functions need to increase fields
        // to calculate each variable offsets. It can be improved later.
        fields.setDim(0);

        uint offset = structsize;
        foreach (s; *members)
        {
            s.setFieldOffset(this, &offset, false);
        }

        sizeok = Sizeok.done;

        // Calculate fields[i].overlapped
        checkOverlappedFields();
    }

    override bool isAnonymous()
    {
        return isActuallyAnonymous;
    }

    final bool isFuncHidden(FuncDeclaration fd)
    {
        //printf("ClassDeclaration.isFuncHidden(class = %s, fd = %s)\n", toChars(), fd.toPrettyChars());
        Dsymbol s = search(Loc.initial, fd.ident, IgnoreAmbiguous | IgnoreErrors);
        if (!s)
        {
            //printf("not found\n");
            /* Because, due to a hack, if there are multiple definitions
             * of fd.ident, NULL is returned.
             */
            return false;
        }
        s = s.toAlias();
        if (auto os = s.isOverloadSet())
        {
            foreach (sm; os.a)
            {
                auto fm = sm.isFuncDeclaration();
                if (overloadApply(fm, s => fd == s.isFuncDeclaration()))
                    return false;
            }
            return true;
        }
        else
        {
            auto f = s.isFuncDeclaration();
            //printf("%s fdstart = %p\n", s.kind(), fdstart);
            if (overloadApply(f, s => fd == s.isFuncDeclaration()))
                return false;
            return !fd.parent.isTemplateMixin();
        }
    }

    /****************
     * Find virtual function matching identifier and type.
     * Used to build virtual function tables for interface implementations.
     * Params:
     *  ident = function's identifier
     *  tf = function's type
     * Returns:
     *  function symbol if found, null if not
     * Errors:
     *  prints error message if more than one match
     */
    final FuncDeclaration findFunc(Identifier ident, TypeFunction tf)
    {
        //printf("ClassDeclaration.findFunc(%s, %s) %s\n", ident.toChars(), tf.toChars(), toChars());
        FuncDeclaration fdmatch = null;
        FuncDeclaration fdambig = null;

        void searchVtbl(ref Dsymbols vtbl)
        {
            foreach (s; vtbl)
            {
                auto fd = s.isFuncDeclaration();
                if (!fd)
                    continue;

                // the first entry might be a ClassInfo
                //printf("\t[%d] = %s\n", i, fd.toChars());
                if (ident == fd.ident && fd.type.covariant(tf) == 1)
                {
                    //printf("fd.parent.isClassDeclaration() = %p\n", fd.parent.isClassDeclaration());
                    if (!fdmatch)
                        goto Lfd;
                    if (fd == fdmatch)
                        goto Lfdmatch;

                    {
                    // Function type matching: exact > covariant
                    MATCH m1 = tf.equals(fd.type) ? MATCH.exact : MATCH.nomatch;
                    MATCH m2 = tf.equals(fdmatch.type) ? MATCH.exact : MATCH.nomatch;
                    if (m1 > m2)
                        goto Lfd;
                    else if (m1 < m2)
                        goto Lfdmatch;
                    }
                    {
                    MATCH m1 = (tf.mod == fd.type.mod) ? MATCH.exact : MATCH.nomatch;
                    MATCH m2 = (tf.mod == fdmatch.type.mod) ? MATCH.exact : MATCH.nomatch;
                    if (m1 > m2)
                        goto Lfd;
                    else if (m1 < m2)
                        goto Lfdmatch;
                    }
                    {
                    // The way of definition: non-mixin > mixin
                    MATCH m1 = fd.parent.isClassDeclaration() ? MATCH.exact : MATCH.nomatch;
                    MATCH m2 = fdmatch.parent.isClassDeclaration() ? MATCH.exact : MATCH.nomatch;
                    if (m1 > m2)
                        goto Lfd;
                    else if (m1 < m2)
                        goto Lfdmatch;
                    }

                    fdambig = fd;
                    //printf("Lambig fdambig = %s %s [%s]\n", fdambig.toChars(), fdambig.type.toChars(), fdambig.loc.toChars());
                    continue;

                Lfd:
                    fdmatch = fd;
                    fdambig = null;
                    //printf("Lfd fdmatch = %s %s [%s]\n", fdmatch.toChars(), fdmatch.type.toChars(), fdmatch.loc.toChars());
                    continue;

                Lfdmatch:
                    continue;
                }
                //else printf("\t\t%d\n", fd.type.covariant(tf));
            }
        }

        searchVtbl(vtbl);
        for (auto cd = this; cd; cd = cd.baseClass)
        {
            searchVtbl(cd.vtblFinal);
        }

        if (fdambig)
            error("ambiguous virtual function `%s`", fdambig.toChars());

        return fdmatch;
    }

    /****************************************
     */
    final bool isCOMclass() const
    {
        return com;
    }

    bool isCOMinterface() const
    {
        return false;
    }

    final bool isCPPclass() const
    {
        return classKind == ClassKind.cpp;
    }

    bool isCPPinterface() const
    {
        return false;
    }

    /****************************************
     */
    final bool isAbstract()
    {
        enum log = false;
        if (isabstract != Abstract.fwdref)
            return isabstract == Abstract.yes;

        if (log) printf("isAbstract(%s)\n", toChars());

        bool no()  { if (log) printf("no\n");  isabstract = Abstract.no;  return false; }
        bool yes() { if (log) printf("yes\n"); isabstract = Abstract.yes; return true;  }

        if (storage_class & STC.abstract_ || _scope && _scope.stc & STC.abstract_)
            return yes();

        if (errors)
            return no();

        /* https://issues.dlang.org/show_bug.cgi?id=11169
         * Resolve forward references to all class member functions,
         * and determine whether this class is abstract.
         */
        extern (C++) static int func(Dsymbol s, void* param)
        {
            auto fd = s.isFuncDeclaration();
            if (!fd)
                return 0;
            if (fd.storage_class & STC.static_)
                return 0;

            if (fd.isAbstract())
                return 1;
            return 0;
        }

        for (size_t i = 0; i < members.dim; i++)
        {
            auto s = (*members)[i];
            if (s.apply(&func, cast(void*)this))
            {
                return yes();
            }
        }

        /* If the base class is not abstract, then this class cannot
         * be abstract.
         */
        if (!isInterfaceDeclaration() && (!baseClass || !baseClass.isAbstract()))
            return no();

        /* If any abstract functions are inherited, but not overridden,
         * then the class is abstract. Do this by checking the vtbl[].
         * Need to do semantic() on class to fill the vtbl[].
         */
        this.dsymbolSemantic(null);

        /* The next line should work, but does not because when ClassDeclaration.dsymbolSemantic()
         * is called recursively it can set PASS.semanticdone without finishing it.
         */
        //if (semanticRun < PASS.semanticdone)
        {
            /* Could not complete semantic(). Try running semantic() on
             * each of the virtual functions,
             * which will fill in the vtbl[] overrides.
             */
            extern (C++) static int virtualSemantic(Dsymbol s, void* param)
            {
                auto fd = s.isFuncDeclaration();
                if (fd && !(fd.storage_class & STC.static_) && !fd.isUnitTestDeclaration())
                    fd.dsymbolSemantic(null);
                return 0;
            }

            for (size_t i = 0; i < members.dim; i++)
            {
                auto s = (*members)[i];
                s.apply(&virtualSemantic, cast(void*)this);
            }
        }

        /* Finally, check the vtbl[]
         */
        foreach (i; 1 .. vtbl.dim)
        {
            auto fd = vtbl[i].isFuncDeclaration();
            //if (fd) printf("\tvtbl[%d] = [%s] %s\n", i, fd.loc.toChars(), fd.toPrettyChars());
            if (!fd || fd.isAbstract())
            {
                return yes();
            }
        }

        return no();
    }

    /****************************************
     * Determine if slot 0 of the vtbl[] is reserved for something else.
     * For class objects, yes, this is where the classinfo ptr goes.
     * For COM interfaces, no.
     * For non-COM interfaces, yes, this is where the Interface ptr goes.
     * Returns:
     *      0       vtbl[0] is first virtual function pointer
     *      1       vtbl[0] is classinfo/interfaceinfo pointer
     */
    int vtblOffset() const
    {
        return classKind == ClassKind.cpp ? 0 : 1;
    }

    /****************************************
     */
    override const(char)* kind() const
    {
        return "class";
    }

    /****************************************
     */
    override final void addLocalClass(ClassDeclarations* aclasses)
    {
        aclasses.push(this);
    }

    // Back end
    Symbol* vtblsym;

    override final inout(ClassDeclaration) isClassDeclaration() inout
    {
        return this;
    }

    override void accept(Visitor v)
    {
        v.visit(this);
    }
}

/***********************************************************
 */
extern (C++) final class InterfaceDeclaration : ClassDeclaration
{
    extern (D) this(Loc loc, Identifier id, BaseClasses* baseclasses)
    {
        super(loc, id, baseclasses, null, false);
        if (id == Id.IUnknown) // IUnknown is the root of all COM interfaces
        {
            com = true;
            classKind = ClassKind.cpp; // IUnknown is also a C++ interface
        }
    }

    override Dsymbol syntaxCopy(Dsymbol s)
    {
        InterfaceDeclaration id =
            s ? cast(InterfaceDeclaration)s
              : new InterfaceDeclaration(loc, ident, null);
        return ClassDeclaration.syntaxCopy(id);
    }


    override Scope* newScope(Scope* sc)
    {
        auto sc2 = super.newScope(sc);
        if (com)
            sc2.linkage = LINK.windows;
        else if (classKind == ClassKind.cpp)
            sc2.linkage = LINK.cpp;
        else if (classKind == ClassKind.objc)
            sc2.linkage = LINK.objc;
        return sc2;
    }

    /*******************************************
     * Determine if 'this' is a base class of cd.
     * (Actually, if it is an interface supported by cd)
     * Output:
     *      *poffset        offset to start of class
     *                      OFFSET_RUNTIME  must determine offset at runtime
     * Returns:
     *      false   not a base
     *      true    is a base
     */
    override bool isBaseOf(ClassDeclaration cd, int* poffset)
    {
        //printf("%s.InterfaceDeclaration.isBaseOf(cd = '%s')\n", toChars(), cd.toChars());
        assert(!baseClass);
        foreach (b; cd.interfaces)
        {
            //printf("\tX base %s\n", b.sym.toChars());
            if (this == b.sym)
            {
                //printf("\tfound at offset %d\n", b.offset);
                if (poffset)
                {
                    // don't return incorrect offsets
                    // https://issues.dlang.org/show_bug.cgi?id=16980
                    *poffset = cd.sizeok == Sizeok.done ? b.offset : OFFSET_FWDREF;
                }
                // printf("\tfound at offset %d\n", b.offset);
                return true;
            }
            if (isBaseOf(b, poffset))
                return true;
        }
        if (cd.baseClass && isBaseOf(cd.baseClass, poffset))
            return true;

        if (poffset)
            *poffset = 0;
        return false;
    }

    bool isBaseOf(BaseClass* bc, int* poffset)
    {
        //printf("%s.InterfaceDeclaration.isBaseOf(bc = '%s')\n", toChars(), bc.sym.toChars());
        for (size_t j = 0; j < bc.baseInterfaces.length; j++)
        {
            BaseClass* b = &bc.baseInterfaces[j];
            //printf("\tY base %s\n", b.sym.toChars());
            if (this == b.sym)
            {
                //printf("\tfound at offset %d\n", b.offset);
                if (poffset)
                {
                    *poffset = b.offset;
                }
                return true;
            }
            if (isBaseOf(b, poffset))
            {
                return true;
            }
        }

        if (poffset)
            *poffset = 0;
        return false;
    }

    /*******************************************
     */
    override const(char)* kind() const
    {
        return "interface";
    }

    /****************************************
     * Determine if slot 0 of the vtbl[] is reserved for something else.
     * For class objects, yes, this is where the ClassInfo ptr goes.
     * For COM interfaces, no.
     * For non-COM interfaces, yes, this is where the Interface ptr goes.
     */
    override int vtblOffset() const
    {
        if (isCOMinterface() || isCPPinterface())
            return 0;
        return 1;
    }

    override bool isCPPinterface() const
    {
        return classKind == ClassKind.cpp;
    }

    override bool isCOMinterface() const
    {
        return com;
    }

    override inout(InterfaceDeclaration) isInterfaceDeclaration() inout
    {
        return this;
    }

    override void accept(Visitor v)
    {
        v.visit(this);
    }
}

// FWDREF

import dmd.errors;
import dmd.typesem;

final void interfaceSemantic(ClassDeclaration cd)
{
    cd.vtblInterfaces = new BaseClasses();
    cd.vtblInterfaces.reserve(cd.interfaces.length);
    foreach (b; cd.interfaces)
    {
        cd.vtblInterfaces.push(b);
        b.copyBaseInterfaces(cd.vtblInterfaces);
    }
}

extern (C++) void determineBaseClasses(ClassDeclaration cldec, Scope* sc, Scope* scx)
{
    if (cldec.baseClassState == SemState.Done)
        return;
//     assert(cldec.baseClassState != SemState.In);

    cldec.baseClassState = SemState.In;
    void defer() { cldec.baseClassState = SemState.Defer; }

    if (cldec.baseok < Baseok.done)
    {
        /* https://issues.dlang.org/show_bug.cgi?id=12078
            * https://issues.dlang.org/show_bug.cgi?id=12143
            * https://issues.dlang.org/show_bug.cgi?id=15733
            * While resolving base classes and interfaces, a base may refer
            * the member of this derived class. In that time, if all bases of
            * this class can  be determined, we can go forward the semantc process
            * beyond the Lancestorsdone. To do the recursive semantic analysis,
            * temporarily set and unset `_scope` around exp().
            */
        T resolveBase(T)(lazy T exp)
        {
            if (!scx)
            {
                scx = sc.copy();
                scx.setNoFree();
            }
            static if (!is(T == void))
            {
                cldec._scope = scx;
                auto r = exp();
                cldec._scope = null;
                return r;
            }
            else
            {
                cldec._scope = scx;
                exp();
                cldec._scope = null;
            }
        }

        cldec.baseok = Baseok.start;

        // Expand any tuples in baseclasses[]
        for (size_t i = 0; i < cldec.baseclasses.dim;)
        {
            auto b = (*cldec.baseclasses)[i];
            b.type = resolveBase(b.type.typeSemantic(cldec.loc, sc));

            Type tb = b.type.toBasetype();
            if (tb.ty == Ttuple)
            {
                TypeTuple tup = cast(TypeTuple)tb;
                cldec.baseclasses.remove(i);
                size_t dim = Parameter.dim(tup.arguments);
                for (size_t j = 0; j < dim; j++)
                {
                    Parameter arg = Parameter.getNth(tup.arguments, j);
                    b = new BaseClass(arg.type);
                    cldec.baseclasses.insert(i + j, b);
                }
            }
            else
                i++;
        }

        if (cldec.baseok >= Baseok.done)
        {
            //printf("%s already semantic analyzed, semanticRun = %d\n", toChars(), semanticRun);
            if (cldec.semanticRun >= PASS.semanticdone)
                return;
            goto Lancestorsdone;
        }

        // See if there's a base class as first in baseclasses[]
        if (cldec.baseclasses.dim)
        {
            BaseClass* b = (*cldec.baseclasses)[0];
            Type tb = b.type.toBasetype();
            TypeClass tc = (tb.ty == Tclass) ? cast(TypeClass)tb : null;
            if (!tc)
            {
                if (b.type != Type.terror)
                    cldec.error("base type must be `class` or `interface`, not `%s`", b.type.toChars());
                cldec.baseclasses.remove(0);
                goto L7;
            }
            if (tc.sym.isDeprecated())
            {
                if (!cldec.isDeprecated())
                {
                    // Deriving from deprecated class makes this one deprecated too
                    cldec.isdeprecated = true;
                    tc.checkDeprecated(cldec.loc, sc);
                }
            }
            if (tc.sym.isInterfaceDeclaration())
                goto L7;

            for (ClassDeclaration cdb = tc.sym; cdb; cdb = cdb.baseClass)
            {
                if (cdb == cldec)
                {
                    cldec.error("circular inheritance");
                    cldec.baseclasses.remove(0);
                    goto L7;
                }
            }

            /* https://issues.dlang.org/show_bug.cgi?id=11034
                * Class inheritance hierarchy
                * and instance size of each classes are orthogonal information.
                * Therefore, even if tc.sym.sizeof == Sizeok.none,
                * we need to set baseClass field for class covariance check.
                */
            cldec.baseClass = tc.sym;
            b.sym = cldec.baseClass;

            if (tc.sym.baseok < Baseok.done)
                resolveBase(tc.sym.dsymbolSemantic(null)); // Try to resolve forward reference
            if (tc.sym.baseok < Baseok.done)
            {
                //printf("\ttry later, forward reference of base class %s\n", tc.sym.toChars());
                if (tc.sym._scope)
                    tc.sym._scope._module.addDeferredSemantic(tc.sym);
                cldec.baseok = Baseok.none;
            }
        L7:
        }

        // Treat the remaining entries in baseclasses as interfaces
        // Check for errors, handle forward references
        bool multiClassError = false;

        for (size_t i = (cldec.baseClass ? 1 : 0); i < cldec.baseclasses.dim;)
        {
            BaseClass* b = (*cldec.baseclasses)[i];
            Type tb = b.type.toBasetype();
            TypeClass tc = (tb.ty == Tclass) ? cast(TypeClass)tb : null;
            if (!tc || !tc.sym.isInterfaceDeclaration())
            {
                // It's a class
                if (tc)
                {
                    if (!multiClassError)
                    {
                        error(cldec.loc,"`%s`: multiple class inheritance is not supported." ~
                                " Use multiple interface inheritance and/or composition.", cldec.toPrettyChars());
                        multiClassError = true;
                    }

                    if (tc.sym.fields.dim)
                        errorSupplemental(cldec.loc,"`%s` has fields, consider making it a member of `%s`",
                                            b.type.toChars(), cldec.type.toChars());
                    else
                        errorSupplemental(cldec.loc,"`%s` has no fields, consider making it an `interface`",
                                            b.type.toChars());
                }
                // It's something else: e.g. `int` in `class Foo : Bar, int { ... }`
                else if (b.type != Type.terror)
                {
                    error(cldec.loc,"`%s`: base type must be `interface`, not `%s`",
                            cldec.toPrettyChars(), b.type.toChars());
                }
                cldec.baseclasses.remove(i);
                continue;
            }

            // Check for duplicate interfaces
            for (size_t j = (cldec.baseClass ? 1 : 0); j < i; j++)
            {
                BaseClass* b2 = (*cldec.baseclasses)[j];
                if (b2.sym == tc.sym)
                {
                    cldec.error("inherits from duplicate interface `%s`", b2.sym.toChars());
                    cldec.baseclasses.remove(i);
                    continue;
                }
            }
            if (tc.sym.isDeprecated())
            {
                if (!cldec.isDeprecated())
                {
                    // Deriving from deprecated class makes this one deprecated too
                    cldec.isdeprecated = true;
                    tc.checkDeprecated(cldec.loc, sc);
                }
            }

            b.sym = tc.sym;

            if (tc.sym.baseok < Baseok.done)
                resolveBase(tc.sym.dsymbolSemantic(null)); // Try to resolve forward reference
            if (tc.sym.baseok < Baseok.done)
            {
                //printf("\ttry later, forward reference of base %s\n", tc.sym.toChars());
                if (tc.sym._scope)
                    tc.sym._scope._module.addDeferredSemantic(tc.sym);
                cldec.baseok = Baseok.none;
            }
            i++;
        }
        if (cldec.baseok == Baseok.none)
        {
            // Forward referencee of one or more bases, try again later
            cldec._scope = scx ? scx : sc.copy();
            cldec._scope.setNoFree();
            cldec._scope._module.addDeferredSemantic(cldec);
            //printf("\tL%d semantic('%s') failed due to forward references\n", __LINE__, toChars());
            return;
        }
        cldec.baseok = Baseok.done;

        // If no base class, and this is not an Object, use Object as base class
        if (!cldec.baseClass && cldec.ident != Id.Object && cldec.object && !cldec.classKind == ClassKind.cpp)
        {
            void badObjectDotD()
            {
                cldec.error("missing or corrupt object.d");
                fatal();
            }

            if (!cldec.object || cldec.object.errors)
                badObjectDotD();

            Type t = cldec.object.type;
            t = t.typeSemantic(cldec.loc, sc).toBasetype();
            if (t.ty == Terror)
                badObjectDotD();
            assert(t.ty == Tclass);
            TypeClass tc = cast(TypeClass)t;

            auto b = new BaseClass(tc);
            cldec.baseclasses.shift(b);

            cldec.baseClass = tc.sym;
            assert(!cldec.baseClass.isInterfaceDeclaration());
            b.sym = cldec.baseClass;
        }
        if (cldec.baseClass)
        {
            if (cldec.baseClass.storage_class & STC.final_)
                cldec.error("cannot inherit from class `%s` because it is `final`", cldec.baseClass.toChars());

            // Inherit properties from base class
            if (cldec.baseClass.isCOMclass())
                cldec.com = true;
            if (cldec.baseClass.isCPPclass())
                cldec.classKind = ClassKind.cpp;
            if (cldec.baseClass.stack)
                cldec.stack = true;
            cldec.enclosing = cldec.baseClass.enclosing;
            cldec.storage_class |= cldec.baseClass.storage_class & STC.TYPECTOR;
        }

        cldec.interfaces = cldec.baseclasses.tdata()[(cldec.baseClass ? 1 : 0) .. cldec.baseclasses.dim];
        foreach (b; cldec.interfaces)
        {
            // If this is an interface, and it derives from a COM interface,
            // then this is a COM interface too.
            if (b.sym.isCOMinterface())
                cldec.com = true;
            if (cldec.classKind == ClassKind.cpp && !b.sym.isCPPinterface())
            {
                error(cldec.loc, "C++ class `%s` cannot implement D interface `%s`",
                    cldec.toPrettyChars(), b.sym.toPrettyChars());
            }
        }
        interfaceSemantic(cldec);
    }

    cldec.baseClassState = SemState.Done;
Lancestorsdone:
}
