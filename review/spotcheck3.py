"""Lemma 1 at a high-lambda witness; Lemma 3 per-(q,+-) class bound with small primes p<=P2;
special-witness behaviour; |L| vs T_R at larger V'."""
import math, random, bisect
import numpy as np
from math import isqrt
from spotcheck import sieve, lam, check_L

N = 1_000_000
primes = sieve(isqrt(N*N + 1) + 2)
# --- Lemma 1, w with many square roots of 1
for w in (120120, 8*3*5*7*11*13*17 // 17 * 1, 360360 if 360360 <= N else 120120, 2*3*5*7*11*13*17*19 // 19):
    for V in (2000, 30000, 300000):
        b = np.zeros(N + 1, bool)
        for p in primes:
            if p <= V or w % p == 0: continue
            m = p*p
            if m > w*N + 1: break
            b[(-pow(w, -1, m)) % m::m] = True
        b[0] = False
        print(f"Lemma1 w={w} lam={lam(w)} V={V}: true={b.sum()} bound={lam(w)*((N*N+1)/V**2+2*(N+1)/V+1):.0f}")

# --- Lemma 3 per class
def root(q):
    m = q*q; r = next(x for x in range(1, q) if (x*x+1) % q == 0)
    return (r - (r*r+1)*pow(2*r, -1, m)) % m
QS = [q for q in primes if 13 <= q <= 200 and q % 4 == 1]
P2 = 1000; SP = [3, 7, 11, 13]
rng = random.Random(5); worst = 0; nspecial = 0; viol = 0
n = np.arange(N + 1)
for trial in range(30):
    h = rng.choice([x for x in range(rng.randint(1, N-200), N) if x % 25 in (7, 18)][:5])
    # (ii): 25 | h r + 1 only for r = h mod 25
    nsf = np.zeros(N + 1, bool)
    for p in primes:
        if p > P2: break
        if p in (2, 5) or h % p == 0: continue
        m = p*p; nsf[(-pow(h, -1, m)) % m::m] = True
    nsf[0] = False
    for q in QS:
        m = q*q; r = root(q)
        for rr in (r, m - r):
            special = (h - rr) % m == 0
            for tau in range(4):
                if (h % 4)*tau % 4 == 3: continue
                cls = (n % m == rr) & (n % 4 == tau); cls[0] = False
                true = int((nsf & cls).sum())
                M4 = 4*m
                bnd = (N/M4)*(1 - math.prod(1 - p**-2 for p in SP if p != q)) + 2**len([p for p in SP if p != q]) - 1 \
                      + sum(N/(M4*p*p) + 1 for p in primes if 13 < p <= P2 and p != q)
                bnd = min(bnd, N//M4 + 1)
                if special: nspecial += 1; continue
                worst = max(worst, true / bnd)
                if true > bnd: viol += 1
print(f"Lemma3 per-class (non-special h): max true/bound={worst:.3f}, violations={viol}; special classes seen={nspecial}")
for Q, Vp in ((50, 100_000), (50, 1_000_000), (13, 1_000_000)):
    check_L(N, Q, Vp)
