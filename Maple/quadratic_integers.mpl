# Type is [ a, b ] where the element is a + b% in Z[%] (% determined by rem M 4)
`type/quad_int` := proc(f) type(f, [integer, integer]) end;


lift := proc(k :: integer, $) :: quad_int; return [ k, 0 ]; end proc;


qiadd := proc(a :: quad_int, b :: quad_int, $) :: quad_int;
    return [ a[1] + b[1], a[2] + b[2] ];
end proc;


qisub := proc(a :: quad_int, b :: quad_int, $) :: quad_int;
    return [ a[1] - b[1], a[2] - b[2] ];
end proc;


qimul := proc(a :: quad_int, b :: quad_int, M :: integer, $) :: quad_int; 
    # should work even if using symmetric mod?
    if (M mod 4) = 1 then
        return [
            a[1]*b[1] + iquo(M - 1, 4)*a[2]*b[2],
            a[1]*b[2] + a[2]*b[1] + a[2]*b[2]
        ];
    else
        return [ a[1]*b[1] + M*a[2]*b[2], a[1]*b[2] + a[2]*b[1] ];
    fi;
end proc;


qirecip_mod := proc(a :: quad_int, M :: integer, p :: posint, $) :: quad_int;
    local f,g,s,x,div;

    f := a[1] + a[2]*x mod p;
    ASSERT(f <> 0,  "Input must not be zero in R/pR");
    g := `if`(M mod 4 = 1, x^2 - x - iquo(M - 1, 4), x^2 - M);
    div := Gcdex(f, g, x, 's') mod p;
    ASSERT(div = 1, "Something went wrong fr");
    return [ coeff(s, x, 0), coeff(s, x, 1) ];
end proc;


qiconjugate := proc(a :: quad_int, M :: integer, $) :: quad_int;
    # a + bg = a + b/2 + bs/2
    # conj = a + b/2 - bs/2 = a + b/2 + b/2 - b/2 - bs/2 = a + b - bg = [a + b, -b]
    return [ `if`((M mod 4) = 1, a[1] + a[2], a[1]), -a[2] ];
end proc;


qinorm := proc(a :: quad_int, M :: integer, $) :: integer;
    return qimul(a, qiconjugate(a, M), M)[1];
end proc;

qi2maple := proc(a :: quad_int, M :: integer, $)
    return a[1] + a[2]*`if`((M mod 4) = 1, (1 + sqrt(M))/2, sqrt(M));
end proc;


NonQuadResidue := proc(p :: posint, $)
    local n,q;
    ASSERT(irem(p - 1, 2, 'q') = 0, "Need 1 and -1 to be different");
    for n from 2 while n &^ q mod p = 1 do od;
    return n;
end proc;


disjoint := proc(a, b)
    local i,j;
    for i from 1 to nops(a) do for j from 1 to nops(b) do
        if a[i] = b[j] then return false; fi;
    od; od;
    return true;
end proc;


isNonResidue := (M, p) -> M &^ p mod p <> 1;


NextInertPrime := proc(start :: posint, M :: integer) :: posint;
    local p;
    p := nextprime(start);
    while not isNonResidue(M, p) do p := nextprime(p); od;
    return p;
end proc;


QuadraticPrimes := proc(
        M :: integer,
        coprime :: list(posint), # odd primes that we want the output to be coprime to
        odd_primes :: list(posint) := [], # odd primes dividing M
        last_residue :: posint := 0,
        $
    ) :: list(posint), list(posint), posint;
    
    local i,crt_res,crt_mod,b,prime_factors,last_res,primes,valid_primes;
    #option trace;

    if M <> 2 then
        prime_factors := `if`(nops(odd_primes) = 0,
            map(p -> p[1], ifactors(M)[2]),
            odd_primes
        );
        if prime_factors[1] = 2 then
            prime_factors := subsop(1=NULL, prime_factors);
        fi;

        ASSERT(not 2 in prime_factors, "Odd primes should contain only the odd primes int the factorisation of M");
        ASSERT(not 2 in coprime, "All of the primes in coprime must be odd");
        ASSERT(disjoint(prime_factors, coprime), "No element of coprime may divide the input");

        last_res := `if`(last_residue = 0,
            NonQuadResidue(prime_factors[-1]),
            last_residue
        );

        crt_res := [ seq(1, i=1..nops(coprime) + nops(prime_factors)), last_res ];
        crt_mod := [ 8, op(coprime), op(prime_factors) ];
        b := chrem(crt_res, crt_mod);
    else
        b := 8*mul(coprime) + 3;
        prime_factors := [];
        last_res := 0;
    fi;

    primes := map(p -> p[1], ifactors(b)[2]);
    valid_primes := select(p -> M &^ iquo(p - 1, 2) mod p <> 1, primes);

    return valid_primes, prime_factors, last_res;
end proc;


TEST := proc()
    local assert_level,sols,checkCorrect,inp,coprime;
    assert_level := kernelopts(assertlevel=1);

    checkCorrect := proc(M, primes)
        ASSERT(nops(primes) > 0, "NO SOLUTIONS");
        ASSERT(foldl(`and`, true, op(map2(isNonResidue, M, primes))), "ONE OR MORE SOLUTIONS INCORRECT");
    end proc;

    inp := 122;
    coprime := [3,5,7,19];
    printf("Checking %d with %a\n", inp, coprime);
    sols := QuadraticPrimes(inp, coprime);
    checkCorrect(122, sols[1]);

    kernelopts(assertlevel=assert_level);
    return;
end proc;
