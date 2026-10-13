// Rigorous squarefree test for 64-bit integers (deterministic Miller-Rabin + Pollard-Brent).
#pragma once
#include <stdint.h>
#include <stdlib.h>
typedef unsigned __int128 u128;

static inline uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m){ return (uint64_t)((u128)a*b % m); }
static inline uint64_t powmod(uint64_t a, uint64_t e, uint64_t m){
    uint64_t r = 1; a %= m;
    while (e){ if (e&1) r = mulmod(r,a,m); a = mulmod(a,a,m); e >>= 1; }
    return r;
}
// deterministic for all n < 2^64
static int is_prime64(uint64_t n){
    if (n < 2) return 0;
    static const uint64_t sp[] = {2,3,5,7,11,13,17,19,23,29,31,37};
    for (int i=0;i<12;i++){ if (n%sp[i]==0) return n==sp[i]; }
    uint64_t d = n-1; int s = 0; while ((d&1)==0){ d>>=1; s++; }
    static const uint64_t bases[] = {2, 325, 9375, 28178, 450775, 9780504, 1795265022};
    for (int i=0;i<7;i++){
        uint64_t a = bases[i] % n; if (a == 0) continue;
        uint64_t x = powmod(a, d, n);
        if (x==1 || x==n-1) continue;
        int comp = 1;
        for (int r=1;r<s;r++){ x = mulmod(x,x,n); if (x==n-1){ comp=0; break; } }
        if (comp) return 0;
    }
    return 1;
}
static uint64_t isqrt64(uint64_t n){
    uint64_t r = (uint64_t)__builtin_sqrtl((long double)n);
    while (r*r > n) r--;
    while ((r+1)*(r+1) <= n) r++;
    return r;
}
static uint64_t gcd64(uint64_t a, uint64_t b){ while (b){ uint64_t t=a%b; a=b; b=t; } return a; }
// Pollard-Brent: returns a nontrivial factor of composite odd n (not a prime power of tiny prime)
static uint64_t pollard(uint64_t n){
    if (n%2==0) return 2;
    for (uint64_t c=1;;c++){
        uint64_t y = 2, x, g = 1, q = 1, ys = 2; uint64_t r = 1, m = 128;
        do {
            x = y;
            for (uint64_t i=0;i<r;i++) y = (mulmod(y,y,n)+c)%n;
            uint64_t k = 0;
            do {
                ys = y;
                uint64_t lim = (m < r-k) ? m : r-k;
                for (uint64_t i=0;i<lim;i++){
                    y = (mulmod(y,y,n)+c)%n;
                    q = mulmod(q, x>y ? x-y : y-x, n);
                }
                g = gcd64(q, n); k += m;
            } while (k < r && g == 1);
            r <<= 1;
        } while (g == 1);
        if (g == n){
            do { ys = (mulmod(ys,ys,n)+c)%n; g = gcd64(x>ys?x-ys:ys-x, n); } while (g == 1);
        }
        if (g != n) return g;
    }
}
// collect prime factors (with multiplicity) of n into f[], returns count; n has no factor < 1000 when called from sqf
static int factor_rec(uint64_t n, uint64_t *f, int k){
    if (n == 1) return k;
    if (is_prime64(n)){ f[k++] = n; return k; }
    uint64_t r = isqrt64(n);
    if (r*r == n){ k = factor_rec(r,f,k); return factor_rec(r,f,k); }
    uint64_t d = pollard(n);
    k = factor_rec(d, f, k);
    return factor_rec(n/d, f, k);
}
static int small_primes_init = 0; static uint32_t SP[200]; static int NSP = 0;
static void init_small_primes(void){
    if (small_primes_init) return;
    for (uint32_t p=2;p<1000;p++){ int ok=1; for (uint32_t q=2;q*q<=p;q++) if (p%q==0){ok=0;break;} if (ok) SP[NSP++]=p; }
    small_primes_init = 1;
}
// returns 1 if n is squarefree, 0 otherwise. Rigorous for all n < 2^64.
static int is_squarefree64(uint64_t n){
    init_small_primes();
    for (int i=0;i<NSP;i++){
        uint64_t p = SP[i];
        if (n % p == 0){ n /= p; if (n % p == 0) return 0; }
    }
    if (n < 1000000ULL) return 1;            // no prime factor < 1000 and n < 1000^2 => n prime or 1
    if (is_prime64(n)) return 1;
    uint64_t r = isqrt64(n); if (r*r == n) return 0;
    uint64_t f[64]; int k = factor_rec(n, f, 0);
    for (int i=0;i<k;i++) for (int j=i+1;j<k;j++) if (f[i]==f[j]) return 0;
    return 1;
}
