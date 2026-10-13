// Independent verifier for the dyn_colour certificate log (Erdős #848).
// Deliberately uses different algorithms from dyn_colour.c:
//  * B is recomputed with sqrt(-1) mod q^2 obtained directly as g^{q(q-1)/4} mod q^2 (g a quadratic
//    non-residue mod q), not by Hensel lifting; every root is checked.
//  * Squarefreeness of ab+1 is decided by plain trial division by all primes p with p^3 <= n
//    (testing p^2 | n), followed by an exact perfect-square test of the cofactor -- no Miller-Rabin,
//    no Pollard rho.  (If no prime p ≤ n^{1/3} divides n, n has at most two prime factors, so n is
//    squarefree unless it is the square of a prime.)
// It replays the log, checks every structural invariant, and checks every pair that the log
// claims to be non-adjacent.
// Usage: ./verify_log N N0 logfile [threads] [pairs_dump_file]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
typedef unsigned __int128 u128;

static uint64_t mm(uint64_t a, uint64_t b, uint64_t m){ return (uint64_t)((u128)a*b % m); }
static uint64_t pw(uint64_t a, uint64_t e, uint64_t m){ uint64_t r=1%m; a%=m; while(e){ if(e&1) r=mm(r,a,m); a=mm(a,a,m); e>>=1;} return r; }

static uint32_t *P; static uint64_t *Pinv; static uint64_t *Plim; static int NP;
// divisibility by odd p via multiplicative inverse mod 2^64: n % p == 0  <=>  n*inv(p) <= floor((2^64-1)/p)
static int sqfree_td(uint64_t n){
    if (n % 4 == 0) return 0;
    if (n % 2 == 0) n >>= 1;
    for (int i=1;i<NP;i++){
        uint64_t p = P[i];
        if ((u128)p*p*p > n) break;
        if (n * Pinv[i] <= Plim[i]){
            n /= p;
            if (n * Pinv[i] <= Plim[i]) return 0;
        }
    }
    // cofactor n has at most two prime factors (all > cube root of the current n); check square
    uint64_t r = (uint64_t)__builtin_sqrtl((long double)n);
    while ((u128)r*r > n) r--;
    while ((u128)(r+1)*(r+1) <= n) r++;
    if (r > 1 && r*r == n) return 0;
    return 1;
}

typedef struct { uint64_t *a; uint64_t *b; size_t lo, hi; long bad; uint64_t ba, bb; } Job;
static void *worker(void *arg){
    Job *j = arg; j->bad = 0;
    for (size_t i=j->lo;i<j->hi;i++){
        if (!sqfree_td(j->a[i]*j->b[i] + 1)){ j->bad++; j->ba = j->a[i]; j->bb = j->b[i]; }
    }
    return NULL;
}

int main(int argc, char **argv){
    uint64_t N = strtoull(argv[1],0,10), N0 = strtoull(argv[2],0,10);
    FILE *f = fopen(argv[3],"rb"); int T = argc > 4 ? atoi(argv[4]) : 16;
    if (!f){ printf("no log\n"); return 1; }
    // primes up to 2.7e6 (cube root of 2^64 is ~2.64e6)
    uint32_t LIM = 2700000; uint8_t *c = calloc(LIM+1,1); P = malloc(sizeof(uint32_t)*200000); NP=0;
    for (uint32_t i=2;i<=LIM;i++){ if(!c[i]){ P[NP++]=i; for (uint64_t j=(uint64_t)i*i;j<=LIM;j+=i) c[j]=1; } }
    Pinv = malloc(8*NP); Plim = malloc(8*NP);
    for (int i=1;i<NP;i++){ uint64_t p=P[i], x=p; for(int k=0;k<6;k++) x*=2-p*x; Pinv[i]=x; Plim[i]=UINT64_MAX/p; }
    // --- recompute B ---
    uint8_t *isB = calloc((N>>3)+1,1);
    uint8_t *comp = calloc(N+1,1);
    for (uint64_t q=2;q<=N;q++){
        if (comp[q]) continue;
        if (q*q <= N) for (uint64_t j=q*q;j<=N;j+=q) comp[j]=1;
        if (q%4!=1) continue;
        uint64_t q2 = q*q, g=2;
        while (pw(g,(q-1)/2,q) != q-1) g++;
        uint64_t i = pw(g, q*(q-1)/4, q2);
        if ((mm(i,i,q2)+1)%q2 != 0){ printf("root error q=%llu\n",(unsigned long long)q); return 1; }
        for (uint64_t n=i;n<=N;n+=q2) isB[n>>3]|=1<<(n&7);
        for (uint64_t n=q2-i;n<=N;n+=q2) isB[n>>3]|=1<<(n&7);
    }
    free(comp);
    // --- replay ---
    uint64_t K = (N-7)/25+1;
    uint32_t *cls = calloc(N+1,4);           // cls[v] = anchor of v's class (0 = unassigned); anchors map to themselves
    uint32_t **mem = calloc(K,sizeof(uint32_t*)); uint16_t *cnt = calloc(K,2), *cap = calloc(K,2);
    size_t PCAP = 1<<26, np = 0; uint64_t *pa = malloc(8*PCAP), *pb = malloc(8*PCAP);
    long badtotal = 0; uint64_t lastadd = 0, nadd=0, nmove=0, nanch=0; uint64_t nextv = 1;
    #define PAIR(x,y) do{ if(np==PCAP){ PCAP*=2; pa=realloc(pa,8*PCAP); pb=realloc(pb,8*PCAP);} pa[np]=(x); pb[np]=(y); np++; }while(0)
    // load the whole log; the time of a move is the vertex of the next add
    fseek(f,0,SEEK_END); long fsz=ftell(f); fseek(f,0,SEEK_SET);
    size_t nops = fsz/12; uint32_t *ops = malloc(fsz); if (fread(ops,12,nops,f)!=nops){ printf("read error\n"); return 1; }
    uint32_t *optime = malloc(4*nops); { uint32_t t = 0xFFFFFFFFu; for (size_t i=nops;i-->0;){ if (ops[3*i]==1) t = ops[3*i+1]; optime[i]=t; } }
    for (size_t oi=0; oi<nops; oi++){
        uint32_t op=ops[3*oi], a=ops[3*oi+1], b=ops[3*oi+2];
        if (op==3){
            if (a%25!=7 || a>N){ printf("bad anchor %u\n",a); return 1; }
            if (a > N0 && a < lastadd){ printf("late anchor %u\n",a); return 1; }
            cls[a]=a; nanch++; continue;
        }
        uint64_t now = optime[oi];   // time of this operation = vertex being inserted
        if (op==2 && now==0xFFFFFFFFu){ printf("dangling move\n"); return 1; }
        if (op==1){
            if (a <= lastadd){ printf("adds not increasing at %u\n",a); return 1; }
            // every non-anchor vertex of B below a must already have been added
            for (uint64_t v=nextv; v<a; v++) if ((isB[v>>3]>>(v&7)&1) && v%25!=7){ printf("vertex %llu never added\n",(unsigned long long)v); return 1; }
            if (!(isB[a>>3]>>(a&7)&1) || a%25==7 || cls[a]){ printf("bad add %u\n",a); return 1; }
            nextv = (uint64_t)a+1; lastadd = a; nadd++;
        } else if (op==2){
            if (!cls[a] || a%25==7){ printf("bad move %u\n",a); return 1; }
            uint64_t k=(cls[a]-7)/25; int found=0;
            for (int j=0;j<cnt[k];j++) if (mem[k][j]==a){ mem[k][j]=mem[k][--cnt[k]]; found=1; break; }
            if (!found){ printf("move of non-member %u\n",a); return 1; }
            cls[a]=0; nmove++;
        } else { printf("bad op\n"); return 1; }
        // target class must exist at time `now`: anchor b <= max(now, N0) and created
        if (b%25!=7 || cls[b]!=b || (b > N0 && b >= now)){ printf("bad target class %u for %u (now %llu)\n",b,a,(unsigned long long)now); return 1; }
        uint64_t k=(b-7)/25;
        PAIR(a,b);
        for (int j=0;j<cnt[k];j++) PAIR(a,mem[k][j]);
        if (cnt[k]==cap[k]){ cap[k]=cap[k]?cap[k]*2:4; mem[k]=realloc(mem[k],4*cap[k]); }
        mem[k][cnt[k]++]=a; cls[a]=b;
    }
    for (uint64_t v=nextv; v<=N; v++) if ((isB[v>>3]>>(v&7)&1) && v%25!=7){ printf("vertex %llu never added (tail)\n",(unsigned long long)v); return 1; }
    for (uint64_t v=7; v<=N0; v+=25) if (cls[v]!=v){ printf("anchor %llu missing\n",(unsigned long long)v); return 1; }
    // --- check all claimed non-adjacencies in parallel ---
    pthread_t th[64]; Job jb[64];
    for (int t=0;t<T;t++){ jb[t].a=pa; jb[t].b=pb; jb[t].lo=np*t/T; jb[t].hi=np*(t+1)/T; pthread_create(&th[t],0,worker,&jb[t]); }
    for (int t=0;t<T;t++){ pthread_join(th[t],0); badtotal+=jb[t].bad; if (jb[t].bad) printf("ADJACENT pair %llu %llu\n",(unsigned long long)jb[t].ba,(unsigned long long)jb[t].bb); }
    uint64_t nB=0, s1=0, s2=0; for (uint64_t v=1;v<=N;v++) if (isB[v>>3]>>(v&7)&1){ nB++; s1+=v; s2+=v*v; }
    printf("Bstats count=%llu sum=%llu sumsq_mod2^64=%llu\n",(unsigned long long)nB,(unsigned long long)s1,(unsigned long long)s2);
    if (argc > 5){ FILE *o = fopen(argv[5],"wb"); for (size_t i=0;i<np;i++){ uint64_t r2[2]={pa[i],pb[i]}; fwrite(r2,8,2,o);} fclose(o); }
    printf("N=%llu N0=%llu |B|=%llu anchors=%llu adds=%llu moves=%llu pairs_checked=%zu bad=%ld  %s\n",
        (unsigned long long)N,(unsigned long long)N0,(unsigned long long)nB,(unsigned long long)nanch,(unsigned long long)nadd,(unsigned long long)nmove,np,badtotal,
        badtotal==0?"VERIFIED":"INVALID");
    return badtotal!=0;
}
