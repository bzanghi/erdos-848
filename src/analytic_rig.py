"""
Rigorous (interval-arithmetic) re-evaluation of the §3 bounds of NOTE.md.

Every real quantity is computed as an Arb ball (python-flint, 128-bit) and replaced by the exact
rational upper endpoint of the ball; the pattern enumeration is then done in exact rational
arithmetic (fractions.Fraction).  Parameter choices (V, V') are taken from the floating-point
optimiser in analytic_check.py -- any choice is valid, only the evaluation must be rigorous.
Integer-valued pieces (prime counts up to 3e8, floors, λ_max) are exact.
"""
import math, sys, itertools
from fractions import Fraction as F
from flint import arb, ctx
import numpy as np
import analytic_check as ac

ctx.prec = 128

def up(x):
    """exact rational upper bound of an arb ball."""
    m, e = x.upper().man_exp()
    return F(int(m)) * (F(2)**int(e))

# --- rigorous prefix sums of 1/p^2 (all primes, and primes ≡ 1 mod 4) at every 4096th prime ---
STEP = 4096
def build_prefix(primes):
    ck = [arb(0)]
    s = arb(0)
    for i, p in enumerate(primes.tolist()):
        s += arb(1) / (p*p)
        if (i+1) % STEP == 0: ck.append(s)
    return ck
print("building rigorous prefix sums...", file=sys.stderr)
CK_ALL = build_prefix(ac.PR)
CK_1 = build_prefix(ac.PR1)

def prefix(primes, ck, j):
    """Σ_{first j primes} 1/p^2 as an arb ball."""
    b = j // STEP
    s = ck[b]
    for p in primes[b*STEP:j].tolist():
        s += arb(1) / (p*p)
    return s

TAIL = arb(1) / (2*(ac.PMAX - 1))     # Σ_{n > PMAX, n odd} 1/n^2 ≤ 1/(2(PMAX-1))

def S2(a, b, mod1=False):
    """arb upper-bounding Σ_{a < p ≤ b} 1/p^2 (optionally p ≡ 1 mod 4)."""
    primes, ck = (ac.PR1, CK_1) if mod1 else (ac.PR, CK_ALL)
    if b <= a: return arb(0)
    bb = min(b, ac.PMAX)
    i = ac._cnt(primes, a); j = ac._cnt(primes, bb)
    s = prefix(primes, ck, j) - prefix(primes, ck, i) if j > i else arb(0)
    if b > ac.PMAX: s += TAIL
    return s

def PI(x, mod1=False):
    """arb upper bound for π(x) (or #{p ≤ x, p ≡ 1 mod 4})."""
    if x <= ac.PMAX: return arb(ac._cnt(ac.PR1 if mod1 else ac.PR, x))
    return arb("1.25506") * arb(x) / arb(x).log()     # Rosser–Schoenfeld (also bounds the mod-4 count)

DELTA_S1 = arb(1) - (arb(1)-arb(1)/9)*(arb(1)-arb(1)/49)*(arb(1)-arb(1)/121)*(arb(1)-arb(1)/169)
LOG1S2 = (arb(1) + arb(2).sqrt()).log()

def LP(N, V, lam):
    V = arb(V)
    return lam * ((arb(N)*N + 1) / (V*V) + 2*(arb(N)+1)/V + 1)

def T_R(N, Q, Vp):
    s = 2*arb(N)*S2(Q, Vp, mod1=True) + 2*PI(Vp, mod1=True)
    K = (arb(N)*N + 1) / (arb(Vp)*Vp)
    s += K * (arb(1)/2 + (2*arb(N)+1).log() / (2*LOG1S2))
    return s

def best_Vp(N, Q):
    best, bv = float('inf'), None
    for Vp in np.geomspace(float(Q+2), float(max(Q+3, N)), 200):
        Vp = int(Vp)
        s = 2*N*ac.sum1_inv2(Q, Vp) + 2*ac.pi41(Vp) + (N*N+1)/Vp**2*(0.5 + math.log(2*N+1)/(2*math.log(1+math.sqrt(2))))
        if s < best: best, bv = s, Vp
    return bv

def constants_rig(N, P1=1000, Q=1000, P2=1000):
    kf = ac.constants(N, P1, Q, P2)                 # only for the parameter choices V_X, V_C
    V_X, V_C = int(kf['V_X']), int(kf['V_C'])
    Vp = best_Vp(N, Q)
    M = (N-7)//25 + 1
    lam = ac.lam_max(N)
    L4 = N//100 + 1
    small = S2(13, P1); smallC = S2(13, P2)
    npi = ac._cnt(ac.PR, P1) - ac._cnt(ac.PR, 13)
    npi2 = ac._cnt(ac.PR, P2) - ac._cnt(ac.PR, 13)
    cellX_w = arb(N)/100*(DELTA_S1 + small) + 15 + npi
    E_X = arb(N)/25*S2(P1, V_X) + (PI(V_X) - ac._cnt(ac.PR, P1)) + LP(N, V_X, lam)
    qs = [q for q in ac.QS_ALL if q <= Q]
    Rcell_free = sum(2*(N//(4*q*q) + 1) for q in qs)
    Rcell_w = sum((2*(arb(N)/(4*q*q)*(DELTA_S1 + smallC) + 15 + npi2) for q in qs), arb(0))
    E_C = arb(N)*S2(P2, V_C) + (PI(V_C) - ac._cnt(ac.PR, P2)) + LP(N, V_C, lam)
    TR = T_R(N, Q, Vp)
    Sp_cell = sum(2*(N//(100*q*q) + 1) for q in qs)
    SPc, prod = arb(0), 25
    for q in ac.QS_ALL:
        if prod*q*q > N*N + 1: break
        prod *= q*q; SPc += arb(N)/(4*q*q) + 1
    return dict(N=N, M=M, cellX_free=F(L4), cellX_w=up(cellX_w), E_X=up(E_X),
                Rcell_free=F(Rcell_free), Rcell_w=up(Rcell_w), E_C=up(E_C), TR=up(TR),
                Sp_cell=F(Sp_cell), SPc=up(SPc), params=(V_X, V_C, Vp))

BIG = F(10)**200

def part_bound(cells, wtypes, free_val, w_val, E, wtypes_sp=(), sp_extra=F(0)):
    if not cells: return F(0)
    best = sum(min(c, free_val) for _, c in cells)
    W = [(a, F(0)) for a in sorted(wtypes)] + [(a, sp_extra) for a in sorted(wtypes_sp)]
    choices = [(a,) for a in W] + [(a, b) for i, a in enumerate(W) for b in W[i+1:]]
    for ch in choices:
        tot = len(ch) * E
        for t, c in cells:
            if all((s*t) % 4 == 3 for s, _ in ch): v = free_val
            else: v = min(free_val, min(w_val + x for s, x in ch if (s*t) % 4 != 3))
            tot += min(c, v)
        best = min(best, tot)
    return best

def pattern_max(k):
    XY = list(itertools.product((0,1,2), repeat=4)); CS = list(itertools.product((0,1), repeat=4))
    fs = lambda W: frozenset(t for t in range(4) if W >> t & 1)
    def xy_bound(st, W):
        cells = [(t, (k['Sp_cell'] if s == 1 else BIG)) for t, s in enumerate(st) if s]
        return part_bound(cells, W, k['cellX_free'], k['cellX_w'], k['E_X'])
    def c_bound(st, Wn, Ws):
        cells = [(t, BIG) for t, s in enumerate(st) if s]
        if not cells: return F(0)
        return part_bound(cells, Wn, k['Rcell_free'], k['Rcell_w'], k['E_C'], Ws, k['SPc'])
    xyB = {(st, W): xy_bound(st, fs(W)) for st in XY for W in range(16)}
    cB = {(st, W, Ws): c_bound(st, fs(W), fs(Ws)) for st in CS for W in range(16) for Ws in range(16)}
    ma = lambda st: sum(1 << t for t, s in enumerate(st) if s)
    mn = lambda st: sum(1 << t for t, s in enumerate(st) if s == 2)
    mp = lambda st: sum(1 << t for t, s in enumerate(st) if s == 1)
    pre = [(st, ma(st), mn(st), mp(st)) for st in XY]
    worst = F(0)
    for sx, mx, nx, px in pre:
        for sy, my, ny, py in pre:
            for sc in CS:
                mc = ma(sc)
                if not (my | mc) or not (mx | mc): continue
                v = xyB[(sx, my|mc)] + xyB[(sy, mx|mc)] + cB[(sc, nx|ny, px|py)]
                if v > worst: worst = v
    return worst + k['TR']

def UB_rig(N):
    k = constants_rig(N)
    return pattern_max(k), k

def tail_rig(N_INF, P1=1000, Q=1000, P2=1000):
    """rigorous version of grid_check.tail (linear coefficients exact-rational upper bounds)."""
    qs = [q for q in ac.QS_ALL if q <= Q]
    sum_q = sum((arb(1)/(q*q) for q in qs), arb(0))
    small = S2(13, P1); smallC = S2(13, P2)
    allq = S2(12, 10**40, mod1=True)                 # Σ_{q ≥ 13, q ≡ 1 (4)} 1/q^2 (upper)
    lin = dict(cellX_free=F(1,100), cellX_w=up((DELTA_S1+small)/100), E_X=up(S2(P1, 10**40)/25),
               Rcell_free=up(sum_q/2), Rcell_w=up(sum_q/2*(DELTA_S1+smallC)), E_C=up(S2(P2, 10**40)),
               SPc=up(allq/4), Sp_cell=up(sum_q/50), TR=up(2*S2(Q, 10**40, mod1=True)))
    U_lin = pattern_max(lin)
    N = arb(N_INF); L = N.log()
    V = N**(arb(2)/3)
    lam = 4*arb(2)**(arb("1.38402")*L/L.log())
    piV = arb("1.25506")*V/V.log()
    LPv = lam*((N*N+1)/(V*V) + 2*(N+1)/V + 1)
    nq = len(qs)
    nspec = (N*N+1).log()/arb(169).log()
    S_N = (6*(piV + LPv) + 2*piV + ((N*N+1)/(V*V))*(arb(1)/2 + (2*N+1).log()/(2*LOG1S2))
           + 2*ac.pi41(Q) + 2 + 8*(1 + 15 + ac.pi(P1)) + 4*(nq*2*(1 + 15 + ac.pi(P2)) + 2*nspec) + 16*nq + 100)
    tot = up(25*S_N/N) + 25*U_lin
    return tot, 25*U_lin

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'tail':
        tot, ul = tail_rig(int(float(sys.argv[2])))
        print(f"tail rigorous: 25*U_lin <= {float(ul):.6f}, 25*(U_lin + S/N) <= {float(tot):.6f} -> {'OK' if tot < 1 else 'FAIL'}")
    elif mode == 'grid':
        N, N_INF = int(float(sys.argv[2])), int(float(sys.argv[3]))
        allok, worst = True, F(0)
        while N < N_INF:
            for r in (F(7,5), F(5,4), F(23,20), F(11,10), F(21,20), F(51,50)):
                Nb = min(int(N*r), N_INF)
                ub, k = UB_rig(Nb)
                Ma = (N-7)//25 + 1
                if ub < Ma + 1: break
            ok = ub < Ma + 1
            allok &= ok; worst = max(worst, ub/(Ma+1))
            print(f"[{N}, {Nb}] UB_rig(Nb)/(M(Na)+1) <= {float(ub/(Ma+1)):.6f} {'OK' if ok else 'FAIL'} params={k['params']}", flush=True)
            if not ok: break
            N = Nb
        print(f"GRID {'ALL OK' if allok else 'FAILED'}  worst ratio {float(worst):.6f}")
