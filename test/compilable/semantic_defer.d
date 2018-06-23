template XYZ(T)
{
    static if (!is(T == bool))
        alias X = T;
    else
        alias X = T;

    static if (is(X == int))
        alias XYZ = X;
    else
        static assert(0, X.stringof~" is not int");
}

XYZ!int a;

void main()
{
}
