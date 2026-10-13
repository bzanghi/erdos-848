"""
Explicit large-N argument for Erdős #848 (see NOTE.md for the proof; this script evaluates it).

For N in a range [Na, Nb] the script certifies: every clique A ⊆ [1,N] (ab+1 non-squarefree for all
a, b ∈ A, a = b allowed) has |A| ≤ M(N) = #{n ≤ N : n ≡ 7 mod 25}.  It does so by showing
UB(Nb) < M(Na) + 1, where UB(Nb) bounds |A| for every clique A ⊆ [1,Nb] that is contained in
neither P7 nor P18 (cliques inside P7 or P18 trivially have size ≤ M).

Rigour notes: all counts are bounded above by expressions of the form (density)·N + (integer
error); floating-point is used for the density sums with a relative safety factor SAFE applied to
every upper bound, and the final comparison keeps a margin far larger than any rounding error.
"""
import math, sys, functools
import numpy as np

SAFE = 1 + 1e-9

def primes_upto(n):
    s = np.ones(n+1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

PMAX = 3 * 10**8
PR = primes_upto(PMAX)
CUM_INV2 = np.cumsum(1.0 / PR.astype(np.float64)**2)
PR1 = PR[PR % 4 == 1]
CUM1_INV2 = np.cumsum(1.0 / PR1.astype(np.float64)**2)

def _cnt(arr, x): return int(np.searchsorted(arr, x, side='right'))
def pi(x):
    """upper bound for π(x); exact for x ≤ PMAX, else Rosser–Schoenfeld π(x) < 1.25506 x/ln x."""
    if x <= PMAX: return _cnt(PR, x)
    return 1.25506 * x / math.log(x)
def pi41(x):
    """upper bound for #{p ≤ x : p ≡ 1 mod 4}."""
    if x <= PMAX: return _cnt(PR1, x)
    return pi(x)
def tail_odd(a):
    """Σ_{n > a, n odd} 1/n^2 ≤ 1/(2(a-1)) : upper bound for Σ_{p > a} 1/p^2 (a ≥ 3)."""
    return 1.0 / (2*(a-1))
def sum_inv2(a, b):
    """upper bound for Σ_{a < p ≤ b} 1/p^2."""
    if b <= a: return 0.0
    bb = min(b, PMAX)
    i, j = _cnt(PR, a), _cnt(PR, bb)
    s = float(CUM_INV2[j-1] - (CUM_INV2[i-1] if i > 0 else 0.0)) if j > i else 0.0
    if b > PMAX: s += tail_odd(PMAX)
    return s * SAFE
def sum1_inv2(a, b):
    """upper bound for Σ_{a < q ≤ b, q ≡ 1 mod 4} 1/q^2."""
    if b <= a: return 0.0
    bb = min(b, PMAX)
    i, j = _cnt(PR1, a), _cnt(PR1, bb)
    s = float(CUM1_INV2[j-1] - (CUM1_INV2[i-1] if i > 0 else 0.0)) if j > i else 0.0
    if b > PMAX: s += tail_odd(PMAX)
    return s * SAFE

ODDP = [int(p) for p in PR[1:60]]
def lam_max(N):
    """max over w ≤ N of λ(w) = #{u mod w : u^2 ≡ 1 (mod w)} = c(2-part)·2^{ω(odd part)}."""
    best = 1
    for e, c in ((0,1),(1,1),(2,2),(3,4)):
        w = 2**e; k = 0
        while w * ODDP[k] <= N: w *= ODDP[k]; k += 1
        best = max(best, c * 2**k)
    return best

QS_ALL = [int(q) for q in PR1 if q >= 13]

DELTA_S1 = 1 - (1-1/9)*(1-1/49)*(1-1/121)*(1-1/169)   # primes {3,7,11,13}

def LP(N, V, lam):
    """# z ≤ N with p^2 | wz+1 for some prime p > V (any w ≤ N with λ(w) ≤ lam)."""
    return lam * ((N*N + 1) / V**2 + 2*(N+1)/V + 1)

def T_R(N, Q):
    """upper bound for #{n ≤ N : q^2 | n^2+1 for some prime q > Q}, optimised over V'."""
    best = float('inf')
    for Vp in np.geomspace(float(Q+2), float(max(Q+3, N)), 200):
        Vp = float(Vp)
        s = 2*N*sum1_inv2(Q, Vp) + 2*pi41(Vp)
        K = (N*N + 1) / Vp**2
        s += K * (0.5 + math.log(2*N+1) / (2*math.log(1+math.sqrt(2))))
        best = min(best, s)
    return best

def best_V(f, lo, hi):
    cands = np.unique(np.geomspace(float(lo), float(hi), 300))
    vals = [f(float(v)) for v in cands]
    i = int(np.argmin(vals)); return float(cands[i]), vals[i]

@functools.lru_cache(maxsize=None)
def constants(N, P1=1000, Q=1000, P2=1000):
    M = (N-7)//25 + 1
    lam = lam_max(N)
    L4 = N//100 + 1                                     # size of a class mod 100 in [1,N]
    small = sum_inv2(13, P1)                            # Σ_{13<p≤P1} 1/p^2
    # --- P7 / P18 targets ---
    cellX_free = L4
    cellX_w = (N/100)*(DELTA_S1 + small)*SAFE + 15 + (pi(P1) - pi(13))
    V_X, E_X = best_V(lambda V: N/25*sum_inv2(P1, V) + (pi(V) - pi(P1)) + LP(N, V, lam), P1+1, max(P1+2, N))
    # --- R targets (cells: n ≡ τ mod 4) ---
    qs = [q for q in QS_ALL if q <= Q]
    TR = T_R(N, Q)
    Rcell_free = sum(2*(N//(4*q*q) + 1) for q in qs)
    smallC = sum_inv2(13, P2)
    Rcell_w = sum(2*((N/(4*q*q))*(DELTA_S1 + smallC)*SAFE + 15 + (pi(P2) - pi(13))) for q in qs)
    V_C, E_C = best_V(lambda V: N*sum_inv2(P2, V) + (pi(V) - pi(P2)) + LP(N, V, lam), P2+1, max(P2+2, N))
    # --- size of a P7/P18 cell (mod 100) consisting only of special elements (in some S_q, q ≥ 13) ---
    Sp_cell = sum(2*(N//(100*q*q) + 1) for q in qs)      # elements of A in S_q, q > Q, are covered by the single global TR term
    SPc, prod = 0.0, 25
    for q in QS_ALL:                                      # extra class n ≡ h (mod q^2) for a special witness h
        if prod*q*q > N*N + 1: break
        prod *= q*q; SPc += N/(4*q*q) + 1
    return dict(N=N, M=M, lam=lam, L4=L4, cellX_free=cellX_free, cellX_w=cellX_w, E_X=E_X, V_X=V_X,
                Rcell_free=Rcell_free, Rcell_w=Rcell_w, E_C=E_C, V_C=V_C, TR=TR, Sp_cell=Sp_cell, SPc=SPc)

def part_bound(cells, wtypes, free_val, w_val, E, cap, wtypes_sp=(), sp_extra=0.0):
    """cells: list of (type, cap_for_cell); wtypes: available witness residues mod 4.
    min over ≤2 witness residues of Σ_cells min(cap, bound) + (#witnesses)·E."""
    if not cells: return 0.0
    best = sum(min(c, free_val) for _, c in cells)
    # witness = (residue, extra per non-free cell); special witnesses (for R targets) pay sp_extra
    W = [(a, 0.0) for a in sorted(wtypes)] + [(a, sp_extra) for a in sorted(wtypes_sp)]
    choices = [(a,) for a in W] + [(a, b) for i, a in enumerate(W) for b in W[i+1:]]
    for ch in choices:
        tot = len(ch) * E
        for t, c in cells:
            if all((s*t) % 4 == 3 for s, _ in ch): v = free_val
            else: v = min(free_val, min(w_val + x for s, x in ch if (s*t) % 4 != 3))
            tot += min(c, v)
        best = min(best, tot)
    return best

def UB(N, detail=False, **kw):
    """Upper bound on |A| over cliques A ⊆ [1,N] with A ⊄ P7 and A ⊄ P18."""
    k = constants(N, **kw)
    INF = float('inf')
    # states of a P7/P18 cell: 0 empty, 1 nonempty & all elements special, 2 has a non-special element
    import itertools
    XY_states = list(itertools.product((0,1,2), repeat=4))
    C_states = list(itertools.product((0,1), repeat=4))
    # part bound for X (or Y): depends on its cell states and the witness residue set from the others
    def xy_bound(st, W):
        cells = [(t, (k['Sp_cell'] if s == 1 else INF)) for t, s in enumerate(st) if s]
        return part_bound(cells, W, k['cellX_free'], k['cellX_w'], k['E_X'], None)
    def c_bound(st, Wns, Wsp):
        cells = [(t, INF) for t, s in enumerate(st) if s]
        if not cells: return 0.0
        return part_bound(cells, Wns, k['Rcell_free'], k['Rcell_w'], k['E_C'], None, Wsp, k['SPc'])
    masks = range(16)
    xyB = {(st, W): xy_bound(st, frozenset(t for t in range(4) if W >> t & 1)) for st in XY_states for W in masks}
    fs = lambda W: frozenset(t for t in range(4) if W >> t & 1)
    cB = {(st, W, Ws): c_bound(st, fs(W), fs(Ws)) for st in C_states for W in masks for Ws in masks}
    def mask_any(st): return sum(1 << t for t, s in enumerate(st) if s)
    def mask_ns(st): return sum(1 << t for t, s in enumerate(st) if s == 2)
    def mask_sp(st): return sum(1 << t for t, s in enumerate(st) if s == 1)
    worst, arg = -1.0, None
    for sx in XY_states:
        mx, nx, px = mask_any(sx), mask_ns(sx), mask_sp(sx)
        for sy in XY_states:
            my, ny, py = mask_any(sy), mask_ns(sy), mask_sp(sy)
            for sc in C_states:
                mc = mask_any(sc)
                if not (my | mc) or not (mx | mc): continue
                tot = xyB[(sx, my | mc)] + xyB[(sy, mx | mc)] + cB[(sc, nx | ny, px | py)] + k['TR']
                if tot > worst: worst, arg = tot, (sx, sy, sc)
    if detail: return worst, arg, k
    return worst

def check_interval(Na, Nb, **kw):
    ub = UB(Nb, **kw)
    Ma = (Na-7)//25 + 1
    return ub < Ma + 1, ub, Ma

if __name__ == '__main__':
    for a in sys.argv[1:]:
        N = int(float(a))
        w, arg, k = UB(N, detail=True)
        print(f"N={N:.3e} M={k['M']} lam={k['lam']} E_X/M={k['E_X']/k['M']:.4f} E_C/M={k['E_C']/k['M']:.4f} "
              f"TR/M={k['TR']/k['M']:.4f} Sp/M={k['Sp_cell']/k['M']:.4f} UB/M={w/k['M']:.4f} worst={arg}")
