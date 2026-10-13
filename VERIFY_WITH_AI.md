# Independent AI verification kit — Erdős #848

**How to use this.** Give everything below the line to a capable AI system with web access, ideally one with a
code-execution or "data analysis" tool (ChatGPT with Code Interpreter, Gemini, Claude, …). It works best
if the reviewer is *not* the model that produced the work (Claude). Ask it to work through every task and
return the report in the format at the end. Please share the full report, including anything it marks
"unsure", with Ben.

---

## Your role

You are an independent, skeptical referee. A claimed computer-assisted proof of Erdős Problem #848 was
produced with heavy AI assistance and **has not been checked by a human expert**. Your job is to find errors,
not to approve it. A report saying "I found a gap at step X" is the most useful possible outcome. Do not
rubber-stamp: for every claim you mark correct, give the reason or the computation that convinced you. If you
cannot check something, say so explicitly rather than guessing.

## The claim

For every N ≥ 1, if A ⊆ {1, …, N} has ab+1 non-squarefree for **all** a, b ∈ A (a = b allowed), then
|A| ≤ M(N) := #{n ≤ N : n ≡ 7 (mod 25)}. Equality is attained by the residue class 7 mod 25. Sawhney had
proved this for all sufficiently large N; this work claims to cover every N.

**Materials** (all public):
- Repository: https://github.com/bzanghi/erdos-848
- Preprint: `paper/erdos848.pdf` (also attached to release `v0.1-preprint`). Section 5 is the core argument.
- Working note: `NOTE.md`. Verification record: `RESULTS.md`.
- Code: `src/` (C and Python); `pari/` (PARI/GP cross-checks); `lean848/` (Lean 4 proofs of some lemmas).

The proof has three parts:
1. N ≤ 10⁴: exact maximum-clique computation.
2. 9982 ≤ N ≤ 10⁹: a colouring certificate (log in the release), replayed by an independent verifier.
3. N ≥ 5·10⁸: an explicit elementary argument (Section 5), with its inequalities checked numerically on a grid
   up to 10³⁵, plus a tail bound beyond.

## Tasks (do them in order; do as many as you can)

**T1. Problem statement and scope.** Is the stated claim really Erdős #848 as posed on
https://www.erdosproblems.com/848? Note that the a ≠ b variant is explicitly excluded. Does the "for all N"
statement match what the site lists as open ("decidable", i.e. open only up to a finite check)? Briefly check
the literature: has anyone else already resolved #848 for all N?

**T2. Preliminaries (Section 2).** Verify each claim with a short proof:
(a) 4 ∤ n²+1;
(b) a prime p ≡ 3 (mod 4) never divides n²+1;
(c) 25 | n²+1 ⇔ n ≡ ±7 (mod 25);
(d) the "witness facts" of Lemma 3, including that h ≡ ±7 and r ≢ ±7 (mod 25) imply 25 ∤ hr+1;
(e) 4 | wz+1 ⇔ {w, z} ≡ {1, 3} (mod 4).
Spot-check each numerically for small values.

**T3. Large-prime lemma (Lemma 6).** Re-prove it yourself:
#{z ≤ N : p² | wz+1 for some prime p > V} ≤ λ(w)((N²+1)/V² + 2(N+1)/V + 1), where
λ(w) = #{u mod w : u² ≡ 1}. Check in particular that the solutions u of m·u² ≡ 1 (mod w) number at most λ(w).
Then test the bound numerically: pick N = 10⁵, several w (including w with many prime factors, e.g.
w = 120120) and several V, compute the left side by brute force, and compare.

**T4. Lemmas 7–9 (small primes, R-target, Pell).** Check:
- the inclusion–exclusion error bound (15 for 4 primes);
- the treatment of "free" cells mod 4;
- the claim that p = q can be dropped for non-special witnesses;
- the "special witness" extra term;
- the Pell-equation count: positive solutions of x² − k y² = −1 with x ≤ N number at most
  ½ + ln(2N+1)/(2 ln(1+√2)).
Brute-force test T_R(Q) against the true count #{n ≤ N : q² | n²+1 for some prime q > Q} for N ≈ 10⁶.

**T5. The case analysis (Section 5, "Patterns").**
- Is every clique A ⊄ P7, A ⊄ P18 covered?
- Is it legitimate to choose witnesses from the *other* parts?
- Is the tail set L counted correctly (once)?
- Is the argument that one grid point Nb covers the whole interval [Na, Nb] valid?
- Look hard for a missed case or a double-use of an error term.

**T6. Independent numerical re-implementation.** Without reading `src/analytic_*.py` first, implement your own
upper bound UB(N) for cliques not contained in P7 or P18, following the lemmas, and evaluate it at
N = 5·10⁸, 10⁹ and 10¹². Is UB(N) < M(N) + 1? Compare with the paper's numbers: the worst grid ratio is 0.996
on [5·10⁸, 7·10⁸], and UB/M → 0.69 asymptotically.

**T7. Tail (N ≥ 10³⁵).** Check the use of Rosser–Schoenfeld (π(x) < 1.25506 x/ln x) and Robin's bound
(ω(n) ≤ 1.38402 ln n/ln ln n for n ≥ 3), and the claim that each sublinear term divided by N is non-increasing
for N ≥ 10⁸.

**T8. Small N and the certificate (optional; needs compute).** If you can run code: build `src/maxclique_small.c`
and confirm ω(G_N) = M(N) for N ≤ 2000. Or write your own brute-force or clique search for N ≤ 500 in any
language. Run `src/dyn_colour.c` with N = 10⁶ and verify its log with `src/verify_log.c`. Also explain whether the
logic in Section 4 (a cover by M(N) independent sets ⇒ ω ≤ M(N), maintained incrementally) is sound.

**T9. Lean (optional).** If you can run Lean 4: `cd lean848 && lake exe cache get && lake build`. Confirm it
builds with no `sorry`, and that the Lean statements actually say what the paper says.

## Report format

```
VERDICT: [no errors found | fixable issues | fatal error found | could not complete]
For each task T1–T9:
  status: [checked-correct | issue | unsure | not attempted]
  evidence: (your proof sketch / computation / numbers)
  issues: (precise location in the paper or code, severity: fatal / fixable / cosmetic)
Anything else suspicious:
What a human number theorist should look at first:
```
