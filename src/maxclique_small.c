// Exact clique number for Erdős #848 at small N.
// Graph: vertices n in [1,N] with n^2+1 not squarefree; edge a~b (a!=b) iff ab+1 not squarefree.
// Prints, for each N in [Nlo,Nhi], omega(N) and M(N) = #{n<=N : n = 7 mod 25}.
// Branch-and-bound with greedy-colouring bounds (Tomita MCQ style) on bitsets.
// Usage: ./maxclique_small Nhi [Nlo]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;
static int NV, W;            // number of vertices, words per bitset
static u64 *adj;             // NV * W
static int best;
static long long nodes;

static inline int popc(u64 x){ return __builtin_popcountll(x); }

// Expand: candidate set P (bitset), current size sz.
static void expand(u64 *P, int sz){
    nodes++;
    // greedy colouring of P to get bounds; order: vertices in increasing index
    int cnt = 0; for (int w=0; w<W; w++) cnt += popc(P[w]);
    if (cnt == 0){ if (sz > best) best = sz; return; }
    if (sz + cnt <= best) return;
    int *order = malloc(sizeof(int)*cnt), *colour = malloc(sizeof(int)*cnt);
    u64 *U = malloc(sizeof(u64)*W), *Q = malloc(sizeof(u64)*W);
    memcpy(U, P, sizeof(u64)*W);
    int k = 0, col = 0;
    while (k < cnt){
        col++;
        memcpy(Q, U, sizeof(u64)*W);
        for (int w=0; w<W; w++){
            while (Q[w]){
                int b = __builtin_ctzll(Q[w]); int v = w*64+b;
                Q[w] &= Q[w]-1;
                // v gets colour col; remove v and its neighbours from Q
                U[w] &= ~(1ULL<<b);
                for (int x=w; x<W; x++) Q[x] &= ~adj[(size_t)v*W+x];
                order[k] = v; colour[k] = col; k++;
            }
        }
    }
    u64 *NP = malloc(sizeof(u64)*W);
    for (int i=cnt-1; i>=0; i--){
        if (sz + colour[i] <= best) break;
        int v = order[i];
        for (int w=0; w<W; w++) NP[w] = P[w] & adj[(size_t)v*W+w];
        expand(NP, sz+1);
        P[v>>6] &= ~(1ULL<<(v&63));
    }
    free(NP); free(order); free(colour); free(U); free(Q);
}

int main(int argc, char **argv){
    int Nhi = atoi(argv[1]);
    int Nlo = argc > 2 ? atoi(argv[2]) : 1;
    long long L = (long long)Nhi*Nhi + 2;
    // squarefree sieve up to L
    unsigned char *sqf = malloc(L+1); memset(sqf, 1, L+1);
    // primes up to sqrt(L)
    long long R = 1; while ((R+1)*(R+1) <= L) R++;
    unsigned char *comp = calloc(R+1,1);
    for (long long p=2; p<=R; p++){
        if (comp[p]) continue;
        for (long long q=p*p; q<=R; q+=p) comp[q]=1;
        long long p2 = p*p;
        for (long long m=p2; m<=L; m+=p2) sqf[m]=0;
    }
    // vertex list
    int *vert = malloc(sizeof(int)*(Nhi+1)); int nv=0;
    for (int n=1; n<=Nhi; n++) if (!sqf[(long long)n*n+1]) vert[nv++] = n;
    for (int N=Nlo; N<=Nhi; N++){
        // vertices <= N
        NV = 0; while (NV < nv && vert[NV] <= N) NV++;
        int M = (N >= 7) ? (N-7)/25 + 1 : 0;
        if (N > Nlo && !( (long long)N == Nhi || NV==0 || vert[NV-1]==N)) continue; // omega only changes when a vertex is added
        W = (NV+63)/64; if (W==0) W=1;
        adj = calloc((size_t)NV*W, sizeof(u64));
        for (int i=0;i<NV;i++) for (int j=0;j<NV;j++) if (i!=j && !sqf[(long long)vert[i]*vert[j]+1])
            adj[(size_t)i*W + (j>>6)] |= 1ULL<<(j&63);
        u64 *P = calloc(W, sizeof(u64));
        for (int i=0;i<NV;i++) P[i>>6] |= 1ULL<<(i&63);
        best = M > 0 ? M - 1 : 0;   // seek a clique of size >= M (we know P7 gives M)
        nodes = 0;
        expand(P, 0);
        printf("N=%d nv=%d M=%d omega=%d nodes=%lld %s\n", N, NV, M, best, nodes, best==M?"OK":"*** DIFFERENT ***");
        fflush(stdout);
        free(P); free(adj);
    }
    return 0;
}
