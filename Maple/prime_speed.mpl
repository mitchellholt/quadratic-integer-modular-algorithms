DetSpeed := proc(
        n :: posint := 2000,
        small_p :: posint:= 11,
        large_p :: posint := 1031,
        filename :: string := "primes_out",
        repeat :: posint := 1000)

    local M,i,out;

    out := fopen(filename, WRITE);
    M := LinearAlgebra[RandomMatrix](n, n, generator=rand(0..2^16));

    for i to repeat do
        fprintf(out, "%d %f\n", small_p, time[real](LinearAlgebra[Determinant](M, method=modular[small_p])));
        fprintf(out, "%d %f\n", large_p, time[real](LinearAlgebra[Determinant](M, method=modular[large_p])));
    od;

    fclose(out);
    return;
end proc;


PrimeSpeedDist := proc(
        n :: posint := 2000,
        filename :: string := "speed_out",
        repeat :: posint := 100)

    local M,i,out,primes,k;

    out := fopen(filename, WRITE);
    M := LinearAlgebra[RandomMatrix](n, n, generator=rand(0..2^32 - 1));

    primes := table();

    for i to repeat do
        for k from 3 to 31 by 2 do
            if not assigned(primes[k]) then primes[k] := nextprime(2^k); fi;
            fprintf(
                out,
                "%d %f\n",
                primes[k],
                time[real](LinearAlgebra[Determinant](M, method=modular[primes[k]]))
            );
        od;
        if irem(i, 10) = 0 then printf("Finished %3d\n", i); fi;
    od;

    fclose(out);
    return;

end proc;
