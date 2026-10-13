"""
Cover every N >= N_START by the explicit argument of analytic_check.py.

1. Grid: N_0 = N_START < N_1 < ... < N_k = N_INF with UB(N_{i+1}) < M(N_i) + 1.  For N in
   [N_i, N_{i+1}] any clique A ⊆ [1,N] is a clique in [1,N_{i+1}] with the same pattern, so
   |A| ≤ UB(N_{i+1}) < M(N_i) + 1 ≤ M(N) + 1 unless A ⊆ P7 or A ⊆ P18.
2. Tail N >= N_INF: UB(N) ≤ U_lin·N + S(N) with U_lin the pattern maximum of the linear
   coefficients and S(N) an explicit sublinear term with S(N)/N non-increasing for N ≥ 10^8
   (see NOTE.md).  Since M(N)+1 > N/25 it suffices that U_lin + S(N_INF)/N_INF < 1/25.
"""
import math, sys, itertools
import analytic_check as ac

N_START = int(float(sys.argv[1])) if len(sys.argv) > 1 else 5*10**8
N_INF = int(float(sys.argv[2])) if len(sys.argv) > 2 else 10**40

def grid():
    N = N_START
    rows = []
    while N < N_INF:
        # largest step (ratio from a short list) that still passes
        for r in (2.0, 1.6, 1.4, 1.25, 1.15, 1.1, 1.05, 1.02, 1.01):
            Nb = min(int(N*r), N_INF)
            ok, ub, Ma = ac.check_interval(N, Nb)
            if ok: break
        if not ok:
            print(f"GRID FAIL at N={N}: UB({Nb})={ub:.6g} vs M+1={Ma+1}"); return False, rows
        rows.append((N, Nb, ub, Ma))
        print(f"[{N:.4e}, {Nb:.4e}]  UB(Nb)/(M(Na)+1) = {ub/(Ma+1):.4f}", flush=True)
        N = Nb
    return True, rows

def tail(P1=1000, Q=1000, P2=1000):
    """U_lin + S(N_INF)/N_INF < 1/25 ?"""
    S = ac.SAFE
    qs = [q for q in ac.QS_ALL if q <= Q]
    sum_q = sum(1/q**2 for q in qs) * S
    small = ac.sum_inv2(13, P1); smallC = ac.sum_inv2(13, P2)
    lin = dict(
        cellX_free = 1/100,
        cellX_w = (ac.DELTA_S1 + small)/100 * S,
        E_X = ac.sum_inv2(P1, float('inf') if False else 10**30) / 25,
        Rcell_free = 2*sum_q/4,
        Rcell_w = 2*sum_q/4*(ac.DELTA_S1 + smallC) * S,
        E_C = ac.sum_inv2(P2, 10**30),
        SPc = sum(1/(4*q*q) for q in ac.QS_ALL) * S + ac.tail_odd(ac.PMAX)/4,
        Sp_cell = 2*sum_q/100,
        TR = 2*ac.sum1_inv2(Q, 10**30),
    )
    U_lin = pattern_max(lin)
    # --- sublinear part at N = N_INF, with V = V' = N^(2/3) ---
    N = N_INF; L = math.log(N)
    V = N**(2/3)
    # Robin (1983): ω(n) ≤ 1.38402·ln n/ln ln n (n ≥ 3), and λ(w) ≤ 4·2^{ω(w)}; this envelope makes
    # λ·N^{-1/3} non-increasing for ln ln N > 2.88, so S(N)/N is non-increasing for N ≥ N_INF.
    lam = 4*2**(1.38402*L/math.log(L))
    piV = 1.25506*V/math.log(V)
    LPv = lam*((N*N+1)/V**2 + 2*(N+1)/V + 1)
    nq = len(qs)
    n_special_q = math.log(N*N+1)/math.log(169)
    S_N = (4*(piV + LPv) + 2*(piV + LPv)                      # ≤ 4 X/Y and ≤ 2 R witness applications
           + 2*1.25506*V/math.log(V)                         # 2π(V') in T_R
           + ((N*N+1)/V**2)*(0.5 + math.log(2*N+1)/(2*math.log(1+math.sqrt(2))))   # Pell part of T_R
           + 2*ac.pi41(Q) + 2                                # "+2" terms of T_R for q ≤ ... (absorbed generously)
           + 8*(1 + 15 + ac.pi(P1))                          # X/Y cells: +1 in L4, incl.-excl. 15, medium +1's
           + 4*(nq*2*(1 + 15 + ac.pi(P2)) + 2*n_special_q)   # R cells
           + 8*nq*2                                          # special-only cells
           + 100)
    val = U_lin + S_N/N
    print(f"tail: U_lin*25 = {U_lin*25:.5f}, S(N_INF)/N_INF*25 = {S_N/N*25:.3e}, total*25 = {val*25:.5f}  -> {'OK' if val < 1/25 else 'FAIL'}")
    return val < 1/25

def pattern_max(k):
    """same enumeration as analytic_check.UB but on per-unit-N coefficients (errors linear parts only)."""
    INF = float('inf')
    XY_states = list(itertools.product((0,1,2), repeat=4))
    C_states = list(itertools.product((0,1), repeat=4))
    fs = lambda W: frozenset(t for t in range(4) if W >> t & 1)
    def xy_bound(st, W):
        cells = [(t, (k['Sp_cell'] if s == 1 else INF)) for t, s in enumerate(st) if s]
        return ac.part_bound(cells, W, k['cellX_free'], k['cellX_w'], k['E_X'], None)
    def c_bound(st, Wns, Wsp):
        cells = [(t, INF) for t, s in enumerate(st) if s]
        if not cells: return 0.0
        return ac.part_bound(cells, Wns, k['Rcell_free'], k['Rcell_w'], k['E_C'], None, Wsp, k['SPc'])
    xyB = {(st, W): xy_bound(st, fs(W)) for st in XY_states for W in range(16)}
    cB = {(st, W, Ws): c_bound(st, fs(W), fs(Ws)) for st in C_states for W in range(16) for Ws in range(16)}
    ma = lambda st: sum(1 << t for t, s in enumerate(st) if s)
    mn = lambda st: sum(1 << t for t, s in enumerate(st) if s == 2)
    mp = lambda st: sum(1 << t for t, s in enumerate(st) if s == 1)
    worst = 0.0
    for sx in XY_states:
        for sy in XY_states:
            for sc in C_states:
                mx, my, mc = ma(sx), ma(sy), ma(sc)
                if not (my | mc) or not (mx | mc): continue
                worst = max(worst, xyB[(sx, my|mc)] + xyB[(sy, mx|mc)] + cB[(sc, mn(sx)|mn(sy), mp(sx)|mp(sy))] + k['TR'])
    return worst

if __name__ == '__main__':
    ok_t = tail()
    ok_g, rows = grid()
    print("ALL OK" if (ok_t and ok_g) else "NOT OK")
