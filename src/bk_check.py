# Independent small-N check (pure Python, Bron–Kerbosch with pivoting, sympy-free squarefree test).
import sys
def sqf(n):
    d = 2
    while d*d <= n:
        if n % (d*d) == 0: return False
        if n % d == 0: n //= d
        d += 1
    return True
def omega(V, adj):
    best = 0
    def bk(R, P, X):
        nonlocal best
        if not P and not X:
            best = max(best, R); return
        if R + len(P) <= best: return
        u = max(P | X, key=lambda w: len(adj[w] & P))
        for v in list(P - adj[u]):
            bk(R+1, P & adj[v], X & adj[v]); P = P - {v}; X = X | {v}
    bk(0, set(V), set())
    return best
Nmax = int(sys.argv[1])
B = [n for n in range(1, Nmax+1) if not sqf(n*n+1)]
adj = {a: {b for b in B if b != a and not sqf(a*b+1)} for a in B}
bad = 0
for N in range(1, Nmax+1):
    if N > 1 and N not in adj and (N-7) % 25 != 0: continue
    V = [b for b in B if b <= N]
    sub = {a: adj[a] & set(V) for a in V}
    w = omega(V, sub); M = (N-7)//25 + 1 if N >= 7 else 0
    if w != M: bad += 1; print("MISMATCH", N, w, M)
print("checked up to", Nmax, "mismatches", bad)
