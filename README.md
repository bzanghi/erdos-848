# Erdős Problem #848 holds for every N

**Claim.** For every N ≥ 1, the largest A ⊆ {1,…,N} such that ab+1 is never squarefree (a, b ∈ A, a = b
allowed) has exactly #{n ≤ N : n ≡ 7 (mod 25)} elements, so the residue class 7 mod 25 is optimal. This is
[Erdős Problem #848](https://www.erdosproblems.com/848) (Erdős–Sárközy). Sawhney proved it for all sufficiently
large N; the best previous explicit threshold was exp(1420). This repository covers every N.

**Status: preprint, not yet refereed.** Scrutiny is very welcome; please open an issue.

**AI disclosure.** This work was done with substantial assistance from Claude (Anthropic). It wrote the code
and drafted the argument and the paper. An independent AI re-implementation of the analytic part (`review/`)
was written without access to `src/analytic_*`. No human expert has yet checked the argument.

## Proof structure

| range | method | verified by |
|---|---|---|
| 1 ≤ N ≤ 10⁴ | exact clique numbers (`src/maxclique_small.c`) | independent Bron–Kerbosch to 5000 (`src/bk_check.py`) |
| 9982 ≤ N ≤ 10⁹ | dynamic colouring certificate (`src/dyn_colour.c`) | independent replay (`src/verify_log.c`, trial division only) and PARI/GP (`pari/`) |
| N ≥ 5·10⁸ | explicit elementary inequalities (paper §5) | Arb interval arithmetic + exact rationals (`src/analytic_rig.py`); independent AI re-implementation (`review/my_ub.py`) |

Read `paper/erdos848.pdf` first. `NOTE.md` is the working note; `RESULTS.md` is the verification record;
`results/` contains the raw outputs.

## Lean formalisation (in progress)

`lean848/` is a Lean 4 + Mathlib project. Build it with `cd lean848 && lake exe cache get && lake build`. Every
result below is proved with no `sorry`, and `#print axioms` shows only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`):

- the witness facts mod 25 and mod 4 (paper Lemma 3);
- `4 ∤ n²+1`; `p ≡ 3 (mod 4)` ⇒ `p ∤ n²+1`; `25 ∣ n²+1 ⇔ n ≡ ±7 (mod 25)`;
- the residue class 7 mod 25 is admissible;
- **the large-prime lemma** (paper Lemma 6), integer form `large_prime_count`;
- the large-prime lemma in the paper's real form, `large_prime_count_real`: for `1 ≤ w ≤ N` and real `V ≥ 1`,
  `#{z ∈ [1,N] : ∃ prime p > V, p² ∣ wz+1} ≤ λ(w)·((N²+1)/V² + 2(N+1)/V + 1)` (via `sum_inv_sqrt_le`:
  `Σ_{m≤K} m^{-1/2} ≤ 2√K`);
- **inclusion–exclusion with bounded error** (core of paper Lemma 7), `ie_count_le` / `ie_count_abs`: for
  `Z = {z ∈ [1,N] : z ≡ c (mod q)}` and residue conditions `z ≡ r_i (mod d_i)`, `i ∈ S`, with the `d_i` pairwise
  coprime and coprime to `q`, the number of `z ∈ Z` meeting some condition is within `2^|S| − 1` of
  `N/q·(1 − Π(1 − 1/d_i))`; prime-square form `ie_prime_squares` (`d_p = p²`, `p ∈ S` prime, `p ∤ q`);
- **the negative Pell count** (used in paper Lemma 8), `pell_neg_count`: for `k ≥ 2`,
  `#{x ∈ [1,N] : ∃ y, x² + 1 = k y²} ≤ 1/2 + log(2N+1)/(2 log(1+√2))`. The proof is elementary (no unit
  theory): two solutions `x < x'` satisfy `η' ≥ (1+√2)² η` with `η = x + y√k` (`pell_ratio`), and
  `1+√2 ≤ η ≤ 2x+1`.

Not yet formalised: the assembly of Lemmas 7 and 9 from these pieces (union bound over mid-range primes, the
special prime `q`), the rest of Lemma 8 (the `q ≤ V'` progressions and the reduction
`n²+1 = kq²`), the pattern
argument, and the link to the numerical certificates.

## Verify with your own AI

See [`VERIFY_WITH_AI.md`](VERIFY_WITH_AI.md): a paste-ready referee brief for an independent AI system, with tasks and a report format.

## Reproduce

`./reproduce.sh` takes about 1.5 h on 16 cores and needs a C compiler, Python 3 (numpy, python-flint), PARI/GP
and zstd. The 10⁹ certificate log (1.3 GB; 520 MB zstd) is attached to the GitHub release. Its
SHA-256 (uncompressed) is
`51b6004a033da8b3f35df0cb39ad9bfbfa6bcb201f02ce1418474f147972b465`.

## Credits

This builds on work by M. Sawhney, W. van Doorn, D. Weisenberg, B. Alexeev, S. Cambie and N. Sothanaphan on the
problem's forum thread, and on T. Bloom's erdosproblems.com.

## License

Code: MIT. Paper and documentation: CC BY 4.0. © 2026 Ben Zanghi.
