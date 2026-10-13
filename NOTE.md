# Erdős Problem #848 — a complete (computer-assisted) resolution

**Problem** ([erdosproblems.com/848](https://www.erdosproblems.com/848), Erdős–Sárközy, [Er92b, p.239]).
Is the maximum size of a set A ⊆ {1,…,N} such that ab+1 is never squarefree (for all a, b ∈ A) achieved by
taking those n ≡ 7 (mod 25)?

**Status before this note.** Sawhney proved the answer is yes for all sufficiently large N. GPT‑5.x/Gemini
pipelines (Sothanaphan et al., March 2026) made the threshold explicit, at N₀ = exp(1420). Direct computation had
reached N of a few hundred. The site listed the problem as *decidable* (resolved up to a finite check).

**Claim.** For every N ≥ 1, every such A has |A| ≤ M(N) := #{n ≤ N : n ≡ 7 (mod 25)}, and {n ≤ N : n ≡ 7 (25)}
attains it. So the answer is **yes for every N**, not only for sufficiently large N.

The proof has three regimes:

| range | method | artifact |
|---|---|---|
| 1 ≤ N ≤ 10⁴ | exact maximum clique (branch and bound), cross-checked by an independent Bron–Kerbosch to N = 5000 | `maxclique_small.c`, `bk_check.py` |
| 9982 ≤ N ≤ 10⁹ | explicit colouring certificate, replayed by an independent verifier | `dyn_colour.c`, `verify_log.c` |
| N ≥ 5·10⁸ | explicit analytic inequalities, evaluated on a grid up to 10³⁵, plus a monotone tail bound beyond | `analytic_check.py`, `grid_check.py` |

**Scope.** We use the reading in which a = b is allowed, as on erdosproblems.com ("for all a, b ∈ A"). Then
every element satisfies a²+1 non-squarefree, and this vertex restriction is used essentially, e.g. in the
pure-R bound. The variant requiring only a ≠ b is *not* covered. StijnC observed that it already differs at
small N: {19, 33, 35, 46, 53} works there.

---

## 0. Set-up

The *compatibility graph* G_N has as vertices the n ≤ N with n²+1 not squarefree; a ~ b (a ≠ b) iff ab+1 is
not squarefree. Admissible sets A are exactly the cliques of G_N, so the claim is ω(G_N) = M(N).

* 4 ∤ n²+1, and p² ∤ n²+1 for p ≡ 3 (mod 4). Also 25 | n²+1 ⟺ n ≡ ±7 (mod 25). Hence the vertex set splits
  into P7 = {n ≡ 7 (25)}, P18 = {n ≡ 18 (25)} and R = (all other vertices) ⊆ ⋃_{q ≥ 13, q ≡ 1 (4)} S_q, where
  S_q = {n : q² | n²+1} is two residue classes mod q².
* P7 is a clique (7·7+1 = 50), so ω ≥ M. P18 is a clique of size ≤ M.
* **Witness facts.** For n, w ≤ N:
  (i) z ∈ P7 ⇒ [25 | wz+1 ⟺ w ∈ P7]; the same holds for P18.
  (ii) h ∈ P7 ∪ P18 and r ∈ R ⇒ 25 ∤ hr+1 (since h⁻¹ ≡ −h mod 25, 25 | hr+1 ⟺ r ≡ h (25)).
  (iii) 4 | wz+1 ⟺ (w mod 4)(z mod 4) ≡ 3 (mod 4).
  So if A is a clique with parts X = A∩P7, Y = A∩P18, C = A∩R, then every element of Y ∪ C is a
  *witness* for X: X lies in its neighbourhood, and that neighbourhood can only use primes p ≠ 5. Similarly
  X ∪ C are witnesses for Y, and X ∪ Y for C. Residues mod 4 decide whether p = 2 is available.

## 1. Small N (N ≤ 10⁴)

`maxclique_small.c` computes ω(G_N) exactly for every N ≤ 10⁴, using Tomita-style colouring bounds on bitsets.
Result: ω(G_N) = M(N) for all N ≤ 10⁴ (`small10k.txt`). `bk_check.py` re-derives this independently for
N ≤ 5000, using pure Python Bron–Kerbosch with pivoting and naive squarefree tests: 0 mismatches.

Note: G_N is *not* M(N)-colourable for every N. At N = 43 the ordering constraints below fail. Small N
therefore needs an exact clique computation.

## 2. Colouring certificate (9982 ≤ N ≤ N_c)

If V(G_N) is covered by M(N) independent sets, then ω(G_N) ≤ M(N). We maintain such a cover *dynamically*.

* Classes are indexed by anchors x ≡ 7 (mod 25). Each P7 vertex is its own anchor.
* At N0 = 9982 (≡ 7 mod 25) all anchors x ≤ N0 exist. Vertices are inserted in increasing order. A vertex v
  joins an existing class (anchor ≤ max(v, N0)) whose members are all non-adjacent to v. If none exists, one
  member u of some class is moved to another class first (a depth-1 augmenting move).
* Invariant: after inserting all vertices ≤ N (N ≥ N0), every class is independent, and every vertex ≤ N lies
  in a class whose anchor is ≤ N. So V(G_N) is covered by M(N) independent sets.

P18 elements are pairwise adjacent and as numerous as anchors. That is why moves are needed: a P18 vertex needs
the unique class still lacking a P18 member.

`dyn_colour.c` decides squarefreeness with trial division by primes < 1000, then deterministic Miller–Rabin
(7 bases, valid for all n < 2⁶⁴), then Pollard–Brent. It logs every ADD/MOVE.

`verify_log.c` is an **independent verifier**. It recomputes the vertex set with a different root algorithm,
√−1 ≡ g^{q(q−1)/4} (mod q²), and checks every root. It checks every claimed non-adjacency by plain trial division
by all primes p ≤ n^{1/3}, followed by a perfect-square test of the cofactor; there is no probabilistic or
Pollard step. It checks every structural invariant: adds strictly increasing, every vertex added before
any larger one, target classes existing at the time of the operation, and moves only of current members.
It rejects tampered logs: redirected adds → adjacent pairs found; a dropped add → "never added".

## 3. Analytic range (N ≥ 5·10⁸)

Fix parameters P1 = P2 = Q = 1000 (we need P2 ≥ Q). For each grid point, the Lemma 1 cutoff V (one value for
P7/P18 targets, one for R targets) and the T_R cutoff V′ are chosen numerically, by minimising the
corresponding error term over a geometric grid of candidates. Any choice is valid. In the tail,
V = V′ = N^{2/3}. An element h ∈ P7 ∪ P18 is *special* if q² | h²+1 for some prime q ≥ 13. Elements special
only through q > Q lie in L and are absorbed by the single global T_R term.

**Lemma 1 (large primes).** For 1 ≤ w ≤ N and V ≥ 1:
#{z ≤ N : p² | wz+1 for some prime p > V} ≤ λ(w)·((N²+1)/V² + 2(N+1)/V + 1), where
λ(w) = #{u mod w : u² ≡ 1 (mod w)}.
*Proof.* Write wz+1 = m p² with m ≤ (wN+1)/V². For fixed m, the admissible p satisfy m p² ≡ 1 (mod w). Given
one solution u₀, the solutions mod w are u₀·s with s² ≡ 1, so they lie in at most λ(w) classes mod w, below
√((wN+1)/m). Sum over m, using Σ_{m≤K} m^{−1/2} ≤ 2√K. ∎
Also λ(w) = c_e·2^{ω(odd part)}, with c_e ∈ {1, 1, 2, 4} for 2^e ∥ w, e = 0, 1, 2, ≥3. So
λ_max(N) = max_{w≤N} λ(w) is computed exactly from primorials.

**Lemma 2 (one witness, P7/P18 target).** Let Z be a residue class mod 100 inside P7 (or P18). Let w ≤ N with
25 ∤ wz+1 and 4 ∤ wz+1 for z ∈ Z. Then
#{z ∈ Z : wz+1 non-squarefree} ≤ (N/100)(δ + Σ_{13<p≤P1} p⁻²) + 15 + (π(P1) − π(13)) + E_X,
where δ = 1 − Π_{p∈{3,7,11,13}}(1 − p⁻²). The first term is exact inclusion–exclusion over {3,7,11,13}, with error
≤ 2⁴ − 1 = 15. The second is a union bound with "+1" per prime. The last term is
E_X = Σ_{P1<p≤V}(N/(25p²) + 1) + Lemma 1. It is paid once per witness for the whole residue class mod 25, so
several cells share it. If (w mod 4)(z mod 4) ≡ 3, the cell is "free" and bounded by ⌊N/100⌋ + 1.

**Lemma 3 (R target).** Let L = {n ≤ N : q² | n²+1 for some prime q > Q}. Then
|L| ≤ T_R(Q) := Σ_{Q<q≤V′, q≡1(4)} (2⌊N/q²⌋ + 2) + ((N²+1)/V′²)·(½ + ln(2N+1)/(2 ln(1+√2))).
The second term holds because n²+1 = k q² with q > V′ forces k ≤ (N²+1)/V′². For each non-square k ≥ 2 the positive
solutions of x² − k y² = −1 are ε^{2j+1}. Here ε is the fundamental unit of the order Z[√k] (for k = 5 it is
2+√5, not the golden ratio), and ε ≥ 1+√2 and ε^{2j+1} ≤ 2x+1. The elements of R ∖ L lie in the
two classes S_q (13 ≤ q ≤ Q). For a witness h ∈ P7 ∪ P18 and a residue τ mod 4, the count of
n ∈ (R∖L), n ≡ τ (4), with hn+1 non-squarefree is bounded per (q, ±) as in Lemma 2. The prime p = q is dropped from that class's prime set: hn+1 is
constant mod q² on the class, so q² ∤ hn+1 for non-special h, and the special case is the SP term below. The global error is
E_C = Σ_{P2<p≤V}(N/p² + 1) + Lemma 1.
*Special witnesses:* if q² | h²+1 for some q ≥ 13, the whole class n ≡ h (mod q²) is compatible with h. We
either use a *non-special* witness, or pay SP = Σ (N/(4q²) + 1) over the smallest such q with
25·Π q² ≤ N²+1.

**Pattern argument.** Let A be a clique with A ⊄ P7 and A ⊄ P18 (otherwise |A| ≤ M trivially). For each part
and each residue τ mod 4, record whether the cell is empty, contains only special elements, or contains a
non-special element; for C, record only whether it is present. In total there are 81·81·16 patterns. For each
part, choose at most 2 witness residues available from the other parts. Each cell is bounded by the minimum of
its trivial bound, its witness bounds (Lemma 2/3), and, for special-only P7/P18 cells,
Σ_{q≤Q} 2(⌊N/(100q²)⌋ + 1). Add T_R(Q) once for all of A ∩ L. The script takes the maximum over patterns of
this bound. Call it UB(N).

**Grid.** For N ∈ [N_i, N_{i+1}], every clique in [1, N] is a clique in [1, N_{i+1}] with the same pattern. So
UB(N_{i+1}) < M(N_i) + 1 covers the whole interval. `grid_check.py` builds such a grid from 5·10⁸ to 10³⁵, with
step ratio ≤ 1.4. The worst ratio is UB/(M+1) = 0.9960, on [5·10⁸, 7·10⁸]; most intervals sit near 0.967. The
asymptotic constant is UB/M → 0.691; the binding pattern is the pure-R one.

**Tail (N ≥ 10³⁵).** UB(N) ≤ U_lin·N + S(N), where U_lin is the pattern maximum of the linear coefficients. All
infinite prime sums are bounded above by an exact sum to 3·10⁸ plus Σ_{n>3·10⁸, n odd} n⁻². S(N) collects
every sublinear term: at most 6 witness applications, each with π(V) + Lemma 1 at V = N^{2/3}; T_R with
V′ = N^{2/3}; and all "+1"/inclusion–exclusion constants. Here π(x) < 1.25506x/ln x (Rosser–Schoenfeld), and
λ(w) ≤ 4·2^{ω(w)} ≤ 4·2^{1.38402 ln N/ln ln N} (Robin 1983). With these envelopes every term of S(N)/N is
non-increasing for N ≥ 10⁸. Since M(N)+1 > N/25, it suffices that 25·(U_lin + S(10³⁵)/10³⁵) < 1. Computed:
0.6907 + 0.0577 = 0.748.

## 4. Verification status (fill in as runs finish)

All regimes are complete and verified; see `RESULTS.md`.

## 5. Caveats

* `analytic_check.py`/`grid_check.py` use floating point. The authoritative evaluation is `analytic_rig.py`:
  every real quantity is an Arb ball (128-bit), replaced by the exact rational upper endpoint, and the pattern
  maximisation is done in exact rational arithmetic. Result: 181 intervals, all OK, worst ratio 0.996034. The
  rigorous tail value is 0.748362. The grid's top endpoint and the tail's start are both the same integer,
  int(float(1e35)) = 99999999999999996863366107917975552 (≈ 10³⁵).
* The argument has not yet been refereed by a human. Independent re-implementations: §1 (two solvers) and §2
  (independent verifier). The independent re-derivation of §3 is recorded in `RESULTS.md`.
