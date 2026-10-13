// PARI/GP cross-check: every pair (a,b) in a binary file of uint64 pairs must have a*b+1 squarefree.
#include <pari/pari.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv){
    pari_init(8000000, 0);
    FILE *f = fopen(argv[1],"rb"); long lo = atol(argv[2]), hi = atol(argv[3]);
    fseek(f, lo*16, SEEK_SET);
    uint64_t buf[2]; long bad=0, n=0;
    for (long i=lo;i<hi;i++){
        if (fread(buf,8,2,f)!=2) break;
        n++;
        if (!uissquarefree(buf[0]*buf[1]+1)){ bad++; fprintf(stderr,"NONSQF %llu %llu\n",(unsigned long long)buf[0],(unsigned long long)buf[1]); }
    }
    printf("%ld %ld %ld %ld\n", lo, hi, n, bad);
    pari_close(); return 0;
}
