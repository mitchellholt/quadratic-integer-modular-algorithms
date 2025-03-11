read("Maple/quadratic_integers.mpl");

# Takahasi & Ishibashi 1961, Cabay 1971
CRTSolve := proc(
        A :: Matrix(integer),
        b :: Vector(integer),
        $) :: Vector(rational);
    local i,n,input_max,p,B,bound,p_prod,k,mod_x,mod_d,d,y;
    #option trace;

    n := nops(A);
    ASSERT(n = nops(b), "Input dimensions must match");

    # Hadamards bound
    input_max := max(max(A), max(b));
    B := ilog10(input_max) + 1;
    bound := trunc(convert(n, float)^(n/2) * 10^(B*n)) + 1;

    # Generate enough primes
    p := table();
    p[1] := nextprime(input_max);
    p_prod := p[1];
    # Invariant: there are k entries in the table
    for k from 1 while p_prod <= 2*bound do
        p[k + 1] := nextprime(p[k]);
        p_prod := p_prod*p[k + 1];
    od;
    ASSERT(assigned(p[k]) and not assigned(p[k + 1]), "Invariant failed");
    p := convert(p, list);

    # Compute modular solutions and determinants
    mod_x := Array(1..k);
    mod_d := Array(1..k);
    for i from 1 to k do
        mod_x[i] := LinearAlgebra[LinearSolve](A, b, method=modular) mod p[i];
        ASSERT(
            LinearAlgebra[Equal](mod_x[i], mod_x[i] mod p[i], compare=entries),
            "um modular linear solver?"
        );
        mod_d[i] := LinearAlgebra[Determinant](A, method=modular[p[i]]); 
        ASSERT(mod_d[i] = mod_d[i] mod p[i], "um modular determinant?");
    od;

    # Use CRT to lift the results
    d := chrem(convert(mod_d, list), p);
    y := chrem([seq( mod_x[i]*mod_d[i] mod p[i], i=1..k )], p);
    return y/d;
end proc;


FracFreeGauss := proc(A :: Matrix, b :: Vector, B, $) :: Matrix;

    #option trace;
    local n,m,T,k,j;

    n,m := op(1, A);
    ASSERT(n = m and n = op(1, b), "Dimensions do not match");

    T := <A|b>;

    # Make upper triangular
    for k from 2 to n do
        # Pivot is T[k-1,k-1]
        for j from k to n do
            T[j,..] := expand(T[k-1,k-1]*T[j,..] - T[j,k-1]*T[k-1,..]);
        od;
    od;

    # Make diagonal
    for k from n - 1 to 1 by -1 do
        for j from k to 1 by -1 do
            T[j,..] := expand(T[k+1,k+1]*T[j,..] - T[j,k+1]*T[k+1,..]);
        od;
    od;

    B := copy(T);

    # Return the solution
    for k to n do T[k,..] := expand(map(rationalize,(T[k,..]/T[k,k]))); od;
    return T[..,n+1];
end proc;


qiModDetGaussSolve := proc(
        A :: Matrix(quad_int),
        b :: Vector(quad_int),
        M :: integer,
        p :: posint,
        $) :: Vector(integer);
    
    #option trace;
    local n,m,T,k,j,fac,det,inv,swap,rows;

    n,m := op(1, A);
    ASSERT(n = m and n = op(1, b), "Dimensions don't match");

    T := <A|b>;
    swap := stack[new]();
    det := 1;
    # Convert to upper-triangular
    for k from 2 to n do
        # Current pivot is T[k-1,k-1] MAKE SURE IT IS NONZERO
        for j from k to n while T[k-1,k-1] = lift(0) do
            if T[j,k-1] <> 0 then
                T[k-1,..], T[j,..] := T[j,..], T[k+1,..];
                stack[push]([k - 1, j], swap);
                det := -det;
            fi;
        od;
        # Determinant is 0
        if j = n + 1 then return lift(0), b fi;

        inv := qirecip_mod(T[k-1,k-1], M, p);
        for j from k to n do
            fac := qimul(inv, T[j,k-1], M) mod p;
            T[j,..] := zip(qisub,
                T[j,..],
                map(a->qimul(a, fac, M) mod p, T[k-1,..])
            ) mod p;
        od;
    od;

    det := det * foldl((a,k) -> qimul(a, T[k,k], M) mod p, lift(1), seq(1..n));
    if det = lift(0) then return lift(0), b fi;

    for k from n - 1 to 1 by -1 do
        # Current pivot is T[k+1,k+1]
        inv := qirecip_mod(T[k+1,k+1], M, p); 
        for j from k to 1 by -1 do
            fac := qimul(inv, T[j,k+1], M) mod p;
            T[j,..] := zip(qisub,
                T[j,..],
                map(a->qimul(a, fac, M) mod p, T[k+1,..])
            ) mod p;
        od;
        T[k+1,..] := map(a->qimul(a, qirecip_mod(T[k+1,k+1], M, p), M) mod p, T[k+1,..]);
    od;
    T[1,..] := map(a->qimul(a, qirecip_mod(T[1,1], M, p), M) mod p, T[1,..]);

    # undo all of the swaps
    while not stack[empty](swap) do
        rows := stack[pop](swap);
        T[rows[1],..], T[rows[2],..] := T[rows[2],..], T[rows[1],..];
    od;

    ASSERT(LinearAlgebra[Equal](T, T mod p, compare=entries), "Mod reductions did not work");
    return det,T[..,n+1];
end proc;


qiCRTSolve := proc(
        A :: Matrix(quad_int),
        b :: Vector(quad_int),
        M :: integer,
        {
            y := NULL, # ptr to store scaled-up integer sols
            d := NULL, # ptr to store determinant
            primes_used := NULL, # ptr to store the primes used
            dense_primes :: boolean := false # if true, use dense inert prime 
                                             # generation (instead of CRT generation)
        },
        $) :: Vector;

    #option trace;

    local
        input_max,B,bound,k,prime,n,m,a,coprime,p_prod,p,valid_primes,d1,d2,dd,
        yy,x,x1,x2,prime_factors,last_res,mod_d,mod_x,i,j;

    n,m := op(1, A);
    ASSERT(n = m and n = op(1, b), "Input dimensions must match");

    # Hadamards bound. TODO: write a theorem for this guy when entries are quadratic integers
    input_max := max(
        max(map(a->qinorm(a, M), A)),
        max(map(a->qinorm(a, M), b))
    );
    B := ilog10(input_max) + 1;
    bound := trunc(convert(n, float)^(n/2) * 10^(B*n)) + 1;

    # Generate enough primes
    p := table();
    k := 0;
    p_prod := 1;
    # Invariant: there are k entries in the table
    while p_prod <= 2*bound do
        if dense_primes then
            prime := NextInertPrime(`if`(assigned(p[k]), p[k], trunc(sqrt(input_max))), M);
            p[++k] := prime;
            p_prod := p_prod*prime;
        else
            valid_primes, prime_factors, last_res := `if`(assigned(prime_factors),
                QuadraticPrimes(M, convert(p, list), prime_factors, last_res),
                QuadraticPrimes(M, convert(p, list))
            );
            for prime in valid_primes do
                p[++k] := prime;
                p_prod := p_prod*prime;
            od;
        fi;
    od;
    ASSERT(assigned(p[k]) and not assigned(p[k + 1]), "Invariant failed");
    p := convert(p, list);

    # Compute modular solutions and determinants
    mod_x := Array(1..k);
    mod_d := Array(1..k);
    for i from 1 to k do
        mod_d[i], mod_x[i] := qiModDetGaussSolve(A mod p[i], b mod p[i], M, p[i]);
        for j to 5 while mod_d[i] = lift(0) do
            if dense_primes then
                p[i] := NextInertPrime(p[k], M);
            else
                p[i] := QuadraticPrimes(M, convert(p, list), prime_factors, last_res)[1][1];
            fi;
            mod_d[i], mod_x[i] := qiModDetGaussSolve(A mod p[i], b mod p[i], M, p[i]);
        od;
        if j = 6 then return FAIL; fi;
    od;

    # Use CRT to recover results
    d1,d2 := map2(op, 1, mod_d), map2(op, 2, mod_d);
    dd := zip((a,b)->[a,b],
        chrem(convert(d1, list), p),
        chrem(convert(d2, list), p)
    );
    x := [seq( map(r->qimul(r, mod_d[i], M) mod p[i], mod_x[i]), i=1..k )];
    x1,x2 := [seq( map2(op, 1, j), j=x )], [seq( map2(op, 2, j), j=x )];
    yy := zip((a,b)->[a,b], chrem(x1, p), chrem(x2, p));

    # convert to Maple
    yy := map(a->qi2maple(a, M), yy);
    dd := qi2maple(dd, M);

    if has([_passed], 'y') then y := copy(yy); fi;
    if has([_passed], 'd') then d := copy(dd); fi;
    if has([_passed], 'primes_used') then primes_used := copy(p); fi;
    return yy/dd;
end proc;


LinearTest := proc(M :: integer := 6)
    local A,b,B,soln,soln2,naive_soln,y,d;
    #option trace;

    # Example 5.2 from algorithms for computer algebra
    A := Matrix([[22, 44, 74], [15, 14, -10], [-25, -28, 20]]);
    b := Vector([1,-2,34]);
    naive_soln := FracFreeGauss(A, b, 'B');
    soln := CRTSolve(A, b);
    soln2 := qiCRTSolve(map(lift, A), map(lift, b), M, 'y'='y', 'd'='d');
    ASSERT(
        LinearAlgebra[Equal](naive_soln, Vector([6, -11/2, 3/2]), compare=entries),
        "Naive method failed"
    );
    ASSERT(
        LinearAlgebra[Equal](soln, Vector([6, -11/2, 3/2]), compare=entries),
        "CRTSolve failed"
    );
    ASSERT(
        LinearAlgebra[Equal](soln2, Vector([6, -11/2, 3/2]), compare=entries),
        "quadratic integer CRT method failed"
    );
    return;
end proc;


qiSolveTest := proc()
    
    #option trace;
    local A,B,AA,b,bb,naive_soln,qi_soln,ans,i,y,d;

    A := Matrix([
        [ [22,-30], [44,-4],   [74, -48]  ],
        [ [15,-1],  [14,44],   [-10, -27] ],
        [ [-25, 5], [-28,-25], [20,58]    ]
    ]);
    b := Vector(3);
    for i to 3 do b[i] := [[1,3], [-2,-3], [34,7]][i]; od;
    AA := map(a->qi2maple(a, 122), A);
    bb := map(a->qi2maple(a, 122), b);

    qi_soln := expand(map(rationalize, qiCRTSolve(A, b, 122, 'y'='y', 'd'='d'))); # is it correct if we rationalise denomiantors?
    naive_soln := expand(map(rationalize, FracFreeGauss(AA, bb, 'B')));
    ans := LinearAlgebra[LinearSolve](AA, bb);
    ASSERT(LinearAlgebra[Equal](ans, qi_soln, compare=entries), "CRT solver");
    ASSERT(LinearAlgebra[Equal](ans, naive_soln, compare=entries), "Frac free solver");
end proc;


qiModGaussSolveTest := proc(M :: integer := 7, n :: integer := 3, cop := [])
    local to_qi,to_quadfld,from_qi,A,B,a,b,det,p,actual,calc_det,ans;

    #option trace;

    to_qi := proc(r,s) return zip((x,y)->[x,y], r, s); end proc;
    to_quadfld := proc(r,s) return zip(
            (x,y)-> x + y*`if`(M mod 4 = 1, (1 + sqrt(M))/2, sqrt(M)),
        r, s);
    end proc;
    from_qi := proc(r) return map(a->qi2maple(a, M), r);
    end proc;

    p := QuadraticPrimes(M, cop)[1][-1];

    det := 0;
    while det = 0 do
        A := LinearAlgebra[RandomMatrix](n, n);
        B := LinearAlgebra[RandomMatrix](n, n);
        det := LinearAlgebra[Determinant](to_quadfld(A, B) mod p) mod p;
    od;
    a := LinearAlgebra[RandomVector](n);
    b := LinearAlgebra[RandomVector](n);

    calc_det, ans := qiModDetGaussSolve(to_qi(A, B) mod p, to_qi(a, b) mod p, M, p);
    actual := LinearAlgebra[LinearSolve](
        to_quadfld(A, B) mod p,
        to_quadfld(a, b) mod p
    ) mod p;
    ASSERT(LinearAlgebra[Equal](actual, from_qi(ans), compare=entries));
    if qi2maple(calc_det, M) <> det then print("Determinant incorrectly computed"); fi;
    return to_quadfld(A,B) mod p, to_quadfld(a,b) mod p;
end proc;


CoolExample := proc(dense_gen :: boolean := false, $)
    #option trace;
    local M,A,B,b,AA,bb,crt_ans,naive_ans,actual_ans,y,d,primes;

    use `mod` = mods in
        M := 122;
        A := Matrix([
            [ [81, -19], [78, -89],  [-81, -80] ],
            [ [22, -53], [-8, 66],   [-43, -19] ],
            [ [50, -30], [-90, 154], [-2, -124] ]
        ]);
        # Kinda cringe we need to do this
        b := Vector(3);
        b[1], b[2], b[3] := [26851, -2700], [-41098, 883], [-67029, 1076];

        AA := map(a->qi2maple(a, M), A);
        bb := map(a->qi2maple(a, M), b);
        printf("Linear solve Ax = b, where A,b are\n");
        print(AA,bb);

        naive_ans := FracFreeGauss(AA,bb,'B');
        crt_ans := expand(map(rationalize,
            qiCRTSolve(A, b, M, 'y'='y', 'd'='d', 'dense_primes'=dense_gen, 'primes_used'='primes')
        ));
        actual_ans := expand(map(rationalize, LinearAlgebra[LinearSolve](AA, bb)));

        printf(
            "Fraction free Guassian elimination (%d bit integers)\n",
            max(map(ilog2,B))
        );
        print(B);
        printf(
            "Modular algorithm using Chinese remaindering (%d bit integers) with primes %a\n",
            max(max(map(ilog2, y)), max(map(ilog2, d))),
            primes
        );
        print(crt_ans);

        ASSERT(
            LinearAlgebra[Equal](naive_ans, actual_ans, compare=entries),
            "Fraction free Gaussian elimination"
        );
        ASSERT(
            LinearAlgebra[Equal](crt_ans, actual_ans, compare=entries),
            "CRT on Quadratic integers"
        );
    end use;
    return;
end proc;
