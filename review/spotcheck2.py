"""Sharper spot-checks: Lemma 1 at large V (where the bound is tight-ish), and the
small-prime part of Lemma 2 (p <= P1) without the large-prime slack."""
import math, random, bisect
import numpy as np
from math import isqrt
from spotcheck import sieve, lam

def run(N, nw, P1, Vs, seed=2):
    rng = random.Random(seed)
    primes = sieve(isqrt(N*N + 1) + 2)
    pi = lambda x: bisect.bisect_right(primes, x)
    delta = 1 - math.prod(1 - p**-2 for p in (3, 7, 11, 13))
    r1 = {V: 0 for V in Vs}; r2 = 0; zcell = np.arange(N + 1) % 100
    tried = 0
    while tried < nw:
        w = rng.randint(N//2, N)            # large w: Lemma 1 hardest
        if w % 25 == 7: continue
        tried += 1
        hits = []                            # (p, z-array start, modulus)
        small = np.zeros(N + 1, bool); bigs = {V: np.zeros(N + 1, bool) for V in Vs}
        for p in primes:
            m = p*p
            if m > w*N + 1: break
            if w % p == 0 or p in (2, 5): continue
            z0 = (-pow(w, -1, m)) % m
            if p <= P1: small[z0::m] = True
            for V in Vs:
                if p > V: bigs[V][z0::m] = True
        for V in Vs:
            b = bigs[V]; b[0] = False
            r1[V] = max(r1[V], b.sum() / (lam(w) * ((N*N + 1)/V**2 + 2*(N + 1)/V + 1)))
        small[0] = False
        for c in (7, 32, 57, 82):
            if ((w % 4) * (c % 4)) % 4 == 3: continue
            true = (small & (zcell == c)).sum()
            bnd = (N/100)*(delta + sum(p**-2 for p in primes if 13 < p <= P1)) + 15 + (pi(P1) - pi(13))
            r2 = max(r2, true / bnd)
    print(f"N={N} #w={nw}: Lemma1 max true/bound by V: " +
          ", ".join(f"V={V}:{r1[V]:.3f}" for V in Vs) + f" | Lemma2 (p<=P1={P1}) max true/bound={r2:.3f}")

run(200_000, 60, 40, [1000, 20_000, 100_000, 200_000])
run(1_000_000, 10, 1000, [10_000, 300_000, 1_000_000])
