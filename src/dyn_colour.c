// Dynamic colouring certificate for Erdős #848.
//
// Graph G_N: vertices n <= N with n^2+1 not squarefree; edge a~b (a != b) iff ab+1 not squarefree.
// Classes are indexed by anchors x == 7 (mod 25).  Vertices are inserted in increasing order.
// Invariant after inserting every vertex <= N (for N >= N0): each vertex <= N lies in a class
// whose anchor is <= max(N, N0), and every class is an independent set.  Hence for every
// N >= N0, V_N is covered by M(N) = #{x <= N : x == 7 mod 25} independent sets, so
// omega(G_N) <= M(N); the residue class 7 mod 25 attains M(N).
// (Between N0 and the first anchor > N0 nothing changes; for N >= N0 the classes with anchors in
// (N, N0] are empty of vertices <= N other than ... -- see note: we require N0 == 7 mod 25.)
//
// To keep the invariant, an inserted vertex may displace one existing member u of a class into
// another class (a depth-1 augmenting move).  Every operation is logged so that an independent
// verifier can replay the whole process and re-check every independence condition.
//
// Log format (binary, uint32 triples):  {op, a, b}
//   op=1: add vertex a to class with anchor b
//   op=2: move vertex a into class with anchor b (removed from its current class)
//   op=3: anchor a created (a == 7 mod 25)
// Usage: ./dyn_colour N N0 seed [logfile]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "sqf64.h"

#define MAXMEM 24
typedef struct { uint8_t cnt; uint32_t mem[MAXMEM]; } Class;   // mem excludes the anchor
static Class *cl;
static uint32_t *where;          // where[v] = class index + 1 for non-anchor vertices (0 = none); sized N+1 (uint32)
static FILE *logf;
static uint32_t *p18of;          // p18of[k] = the member == 18 mod 25 of class k, or 0
static uint64_t *freel, *freepos; static uint64_t nfree = 0;   // classes without a P18 member
static void free_add(uint64_t k){ freepos[k] = nfree; freel[nfree++] = k; }
static void free_del(uint64_t k){ uint64_t p = freepos[k], last = freel[--nfree]; freel[p] = last; freepos[last] = p; }
static uint64_t tests = 0;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void){ rng ^= rng<<13; rng ^= rng>>7; rng ^= rng<<17; return rng; }
static inline uint32_t anchor(uint64_t k){ return (uint32_t)(7 + 25*k); }
static inline int adj(uint64_t a, uint64_t b){ tests++; return !is_squarefree64(a*b + 1); }
static void logop(uint32_t op, uint32_t a, uint32_t b){ if (logf){ uint32_t r[3] = {op,a,b}; fwrite(r,4,3,logf);} }

// number of conflicts of v with class k (anchor + members), stops counting at 2; records the conflicting member
static int conflicts(uint64_t v, uint64_t k, int *idx){
    int c = 0; *idx = -1;
    if (adj(v, anchor(k))) return 99;               // cannot displace the anchor
    Class *C = &cl[k];
    for (int j=0;j<C->cnt;j++){
        if (C->mem[j] == v) continue;
        if (adj(v, C->mem[j])){ c++; *idx = j; if (c >= 2) return c; }
    }
    return c;
}
static void add_to(uint64_t v, uint64_t k){
    Class *C = &cl[k];
    if (C->cnt >= MAXMEM){ fprintf(stderr,"class overflow\n"); exit(3); }
    C->mem[C->cnt++] = (uint32_t)v; where[v] = (uint32_t)(k+1);
    if (v % 25 == 18){ if (p18of[k]){ fprintf(stderr,"two P18 in class\n"); exit(4);} p18of[k] = (uint32_t)v; free_del(k); }
}
static void remove_from(uint64_t k, int j){
    Class *C = &cl[k]; uint32_t u = C->mem[j]; where[u] = 0;
    C->mem[j] = C->mem[--C->cnt];
    if (u % 25 == 18){ p18of[k] = 0; free_add(k); }
}

int main(int argc, char **argv){
    uint64_t N = strtoull(argv[1], 0, 10);
    uint64_t N0 = strtoull(argv[2], 0, 10);
    rng ^= strtoull(argv[3],0,10)*0x9E3779B97F4A7C15ULL; xr(); xr();
    logf = argc > 4 ? fopen(argv[4], "wb") : NULL;
    if (N >= (1ULL<<32) - 1) { fprintf(stderr, "N too large\n"); return 1; }
    if (N0 % 25 != 7){ fprintf(stderr, "N0 must be 7 mod 25\n"); return 1; }
    // --- mark B ---
    uint8_t *isB = calloc((N>>3)+1, 1);
    {
        uint64_t L = N; uint8_t *comp = calloc(L+1,1);
        for (uint64_t p=2; p<=L; p++){
            if (comp[p]) continue;
            if (p*p <= L) for (uint64_t q=p*p; q<=L; q+=p) comp[q]=1;
            if (p % 4 != 1) continue;
            uint64_t i = 0;
            for (uint64_t c=2;;c++){ if (powmod(c,(p-1)/2,p) == p-1){ i = powmod(c,(p-1)/4,p); break; } }
            uint64_t p2 = p*p;
            uint64_t t = (mulmod(i,i,p2) + 1) % p2;
            uint64_t inv2i = powmod((2*i)%p, p-2, p);
            uint64_t k = mulmod((t/p)%p, inv2i, p);
            uint64_t i2 = (i + p2 - (k*p)%p2) % p2;
            if ((mulmod(i2,i2,p2)+1)%p2 != 0){ fprintf(stderr,"hensel fail\n"); return 1; }
            for (uint64_t n=i2; n<=N; n+=p2) isB[n>>3] |= 1<<(n&7);
            for (uint64_t n=p2-i2; n<=N; n+=p2) isB[n>>3] |= 1<<(n&7);
        }
        free(comp);
    }
    uint64_t K = (N-7)/25 + 1, K0 = (N0-7)/25 + 1;
    cl = calloc(K, sizeof(Class));
    where = calloc(N+1, sizeof(uint32_t));
    p18of = calloc(K, sizeof(uint32_t)); freel = malloc(K*sizeof(uint64_t)); freepos = malloc(K*sizeof(uint64_t));
    for (uint64_t k=0;k<K0;k++) free_add(k);
    uint64_t nB=0, nDirect=0, nAug=0, tries_total=0, maxtries=0;
    for (uint64_t k=0;k<K0;k++) logop(3, anchor(k), 0);
    for (uint64_t v=1; v<=N; v++){
        if (!(isB[v>>3] & (1<<(v&7)))) continue;
        nB++;
        if (v % 25 == 7){ if (v > N0){ logop(3, (uint32_t)v, 0); free_add((v-7)/25); } continue; }
        uint64_t Kv = (v <= N0) ? K0 : (v-8)/25 + 1;     // existing classes: anchors <= N0, or anchors < v
        int done = 0; uint64_t tries = 0;
        if (v % 25 == 18){
            // direct: a class with no P18 member
            for (uint64_t a=0; a<nfree && a<400 && !done; a++){
                uint64_t k = (nfree <= 400) ? freel[a] : freel[xr()%nfree]; tries++; int idx;
                if (conflicts(v,k,&idx)==0){ add_to(v,k); logop(1,(uint32_t)v,anchor(k)); done=1; nDirect++; }
            }
            // augment: class k whose only conflict with v is its P18 member u; move u to a free class
            for (int att=0; att<200000 && !done; att++){
                uint64_t k = xr() % Kv; tries++; int idx;
                if (!p18of[k]) continue;
                if (conflicts(v,k,&idx) != 1) continue;
                uint32_t u = cl[k].mem[idx];
                for (uint64_t a=0; a<nfree && a<400; a++){
                    uint64_t k2 = (nfree <= 400) ? freel[a] : freel[xr()%nfree]; int idx2;
                    if (conflicts(u,k2,&idx2)==0){
                        remove_from(k, idx); add_to(u, k2); logop(2, u, anchor(k2));
                        add_to(v, k); logop(1, (uint32_t)v, anchor(k));
                        done = 1; nAug++; break;
                    }
                }
            }
        }
        // 1) direct placement
        for (int att=0; att<200 && !done && v%25!=18; att++){
            uint64_t k = xr() % Kv; tries++; int idx;
            if (conflicts(v, k, &idx) == 0){ add_to(v,k); logop(1,(uint32_t)v,anchor(k)); done=1; nDirect++; }
        }
        // 2) depth-1 augmentation: v conflicts with exactly one member u of class k; move u elsewhere
        for (int att=0; att<20000 && !done && v%25!=18; att++){
            uint64_t k = xr() % Kv; tries++; int idx;
            if (conflicts(v, k, &idx) != 1) continue;
            uint32_t u = cl[k].mem[idx];
            uint64_t Ku = Kv;   // any class existing at the current time
            for (int a2=0; a2<200; a2++){
                uint64_t k2 = xr() % Ku; if (k2 == k) continue; int idx2;
                if (conflicts(u, k2, &idx2) == 0){
                    remove_from(k, idx); add_to(u, k2); logop(2, u, anchor(k2));
                    add_to(v, k); logop(1, (uint32_t)v, anchor(k));
                    done = 1; nAug++; break;
                }
            }
        }
        if (!done){ printf("FAIL at v=%llu (v mod 25 = %llu)\n", (unsigned long long)v, (unsigned long long)(v%25)); return 2; }
        tries_total += tries; if (tries > maxtries) maxtries = tries;
        if ((v & ((1ULL<<26)-1)) == 0){ fprintf(stderr, "v=%llu nB=%llu tests=%llu aug=%llu\n",(unsigned long long)v,(unsigned long long)nB,(unsigned long long)tests,(unsigned long long)nAug); }
    }
    int maxcnt=0; for (uint64_t k=0;k<K;k++) if (cl[k].cnt>maxcnt) maxcnt=cl[k].cnt;
    printf("N=%llu N0=%llu M=%llu vertices=%llu direct=%llu augment=%llu tests=%llu avg_tries=%.2f max_tries=%llu max_members=%d SUCCESS\n",
        (unsigned long long)N,(unsigned long long)N0,(unsigned long long)K,(unsigned long long)nB,(unsigned long long)nDirect,(unsigned long long)nAug,
        (unsigned long long)tests,(double)tries_total/(nDirect+nAug),(unsigned long long)maxtries,maxcnt);
    if (logf) fclose(logf);
    return 0;
}
