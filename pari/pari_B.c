// PARI/GP cross-check: statistics of B = {n in [a,b] : n^2+1 not squarefree}, decided by libpari's uissquarefree.
#include <pari/pari.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv){
    pari_init(8000000, 0);
    unsigned long a = strtoul(argv[1],0,10), b = strtoul(argv[2],0,10);
    unsigned long cnt=0, s1=0, s2=0;
    for (unsigned long n=a; n<=b; n++){
        if (!uissquarefree(n*n+1)){ cnt++; s1 += n; s2 += n*n; }
    }
    printf("%lu %lu %lu %lu %lu\n", a, b, cnt, s1, s2);
    pari_close(); return 0;
}
