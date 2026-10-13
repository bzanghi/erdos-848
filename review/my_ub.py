"""Independent re-derivation of the Section 3 upper bound UB(N) for Erdos #848.

Bounds |A| for cliques A of G_N with A not inside P7 and not inside P18.
Written from NOTE.md lemmas only (analytic_check.py / grid_check.py not read).

Parts: X = A∩P7, Y = A∩P18, C = A∩R. Cells: residue tau mod 4.
|A| <= sum_cells bound(cell \ L) + |L|, with |L| <= T_R.
"""
import math, itertools, sys
import numpy as np

P1 = P2 = Q = 1000
LIM = 20_000_000
SAFE = 1 + 1e-9

def sieve(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

PR = sieve(LIM)
PRf = PR.astype(np.float64)
INV2_CUM = np.cumsum(1.0 / PRf**2)

def pi(x):
    if x < 2: return 0
    if x <= LIM: return int(np.searchsorted(PR, int(x), side='right'))
    return math.floor(1.25506 * x / math.log(x)) + 1          # Rosser-Schoenfeld upper bound

def sum_inv2(lo, hi):
    """upper bound on sum_{lo<p<=hi} p^-2 (primes)."""
    def cum(x):
        k = np.searchsorted(PR, int(min(x, LIM)), side='right')
        return INV2_CUM[k-1] if k else 0.0
    s = cum(hi) - cum(lo)
    if hi > LIM:   # odd n >= LIM+1 : sum 1/n^2 <= 1/a^2 + 1/(2a)
        a = LIM + 1
        s += 1.0/a**2 + 1.0/(2*a)
    return s * SAFE

QS = [int(q) for q in PR if 13 <= q <= Q and q % 4 == 1]
SMALLP = [3, 7, 11, 13]

def lam_max(N):
    best = 1
    odd = [int(p) for p in PR[1:40]]
    for e, c in ((0,1),(1,1),(2,2),(3,4)):
        prod = 2**e; k = 0
        if prod > N: continue
        while prod * odd[k] <= N:
            prod *= odd[k]; k += 1
        best = max(best, c * 2**k)
    return best

def lemma1(N, V):
    return lam_max(N) * ((N*N + 1) / V**2 + 2*(N+1)/V + 1) * SAFE

def best_V(f, N):
    """minimise f(V) over a log grid of V (any V>=P1 is legitimate)."""
    best = None
    for e in np.linspace(math.log10(P1*2), math.log10(N)+0.5, 400):
        V = 10**e; val = f(V)
        if best is None or val < best[0]: best = (val, V)
    return best

def E_X(N):   # once per witness applied to a P7/P18 part (whole class mod 25)
    return best_V(lambda V: N/25*sum_inv2(P1, V) + (pi(V)-pi(P1)) + lemma1(N, V), N)

def E_C(N):   # once per witness applied to C (all n<=N)
    return best_V(lambda V: N*sum_inv2(P2, V) + (pi(V)-pi(P2)) + lemma1(N, V), N)

def T_R(N):
    pell = lambda Vp: (N*N+1)/Vp**2 * (0.5 + math.log(2*N+1)/(2*math.log(1+math.sqrt(2))))
    def f(Vp):
        # sum_{Q<q<=V', q=1 mod 4} (2 floor(N/q^2)+2) <= 2N*sum p^-2 + 2*(pi(V')-pi(Q))
        return 2*N*sum_inv2(Q, Vp) + 2*(pi(Vp)-pi(Q)) + pell(Vp)*SAFE
    return best_V(f, N)

def cell_bounds(N):
    T = N//100 + 1
    SX = sum(2*(N//(100*q*q) + 1) for q in QS)
    delta = 1 - math.prod(1 - 1/p**2 for p in SMALLP)
    WX = (N/100)*(delta + sum_inv2(13, P1)) + 15 + (pi(P1) - pi(13))
    # C cells: R\L within tau mod 4, split over (q,+-) classes mod 4q^2
    CT = 0; CW = 0.0
    inv2_mid = [int(p) for p in PR if 13 < p <= P2]
    for q in QS:
        triv = N//(4*q*q) + 1
        sp = [p for p in SMALLP if p != q]
        m = 4*q*q
        w = (N/m)*(1 - math.prod(1-1/p**2 for p in sp)) + (2**len(sp)-1)
        w += sum(N/(m*p*p) + 1 for p in inv2_mid if p != q)
        CT += 2*triv; CW += 2*min(triv, w*SAFE)
    k, prod, SP = 0, 25, 0
    for q in QS:
        if prod*q*q > N*N+1: break
        prod *= q*q; SP += N//(4*q*q) + 1; k += 1
    return dict(T=T, SX=min(T, SX), WX=WX*SAFE, CT=CT, CW=CW, SP=SP, kSP=k)

def UB(N, verbose=False):
    cb = cell_bounds(N); ex = E_X(N)[0]; ec = E_C(N)[0]; tr = T_R(N)[0]
    T, SX, WX = cb['T'], cb['SX'], cb['WX']
    CT, CW, SP = cb['CT'], cb['CW'], cb['SP']
    covers = lambda W, tau: any((s*tau) % 4 != 3 for s in W)
    subsets = [W for r in range(5) for W in itertools.combinations(range(4), r)]
    # P7/P18 part: states 0 empty, 1 special-only, 2 has non-special
    def part_bound(states, avail):
        best = math.inf
        for W in subsets:
            if not set(W) <= avail: continue
            tot = len(W)*ex
            for tau, s in enumerate(states):
                if s == 0: continue
                base = SX if s == 1 else T
                if covers(W, tau): base = min(base, WX)
                tot += base
            best = min(best, tot)
        return best
    def c_bound(cst, avN, avS):
        best = math.inf
        for W in subsets:
            if not set(W) <= (avN | avS): continue
            tot = sum(ec + (0 if s in avN else SP) for s in W)
            for tau in range(4):
                if cst[tau]: tot += CW if covers(W, tau) else CT
            best = min(best, tot)
        return best
    states = list(itertools.product(range(3), repeat=4))
    cstates = list(itertools.product(range(2), repeat=4))
    res = (-1, None)
    pb_cache = {}
    for xs in states:
        for ys in states:
            for cs in cstates:
                xne, yne, cne = any(xs), any(ys), any(cs)
                if not cne and (not xne or not yne): continue   # A in P7 or P18
                cav = {t for t in range(4) if cs[t]}
                xav = {t for t in range(4) if ys[t]} | cav
                yav = {t for t in range(4) if xs[t]} | cav
                key = (xs, frozenset(xav)); bx = pb_cache.get(key)
                if bx is None: bx = pb_cache[key] = part_bound(xs, xav)
                key = (ys, frozenset(yav)); by = pb_cache.get(key)
                if by is None: by = pb_cache[key] = part_bound(ys, yav)
                avN = {t for t in range(4) if xs[t] == 2 or ys[t] == 2}
                avS = {t for t in range(4) if xs[t] or ys[t]} - avN
                key = (cs, frozenset(avN), frozenset(avS)); bc = pb_cache.get(key)
                if bc is None: bc = pb_cache[key] = c_bound(cs, avN, avS)
                tot = bx + by + bc + tr
                if tot > res[0]: res = (tot, (xs, ys, cs, bx, by, bc))
    M = (N - 7)//25 + 1
    if verbose:
        print(f"N={N:.3e} M={M} UB={res[0]:.6e} UB/M={res[0]/M:.5f} UB<M+1: {res[0] < M+1}")
        print(f"   E_X={ex:.3e} E_C={ec:.3e} T_R={tr:.3e} lam={lam_max(N)} kSP={cb['kSP']} SP={SP:.3e}")
        print(f"   worst pattern X={res[1][0]} Y={res[1][1]} C={res[1][2]} parts={res[1][3]:.3e},{res[1][4]:.3e},{res[1][5]:.3e}")
    return res[0], M

if __name__ == '__main__':
    Ns = [int(float(a)) for a in sys.argv[1:]] or [5*10**8, 10**9, 10**12, 10**20]
    for N in Ns: UB(N, verbose=True)
