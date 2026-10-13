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
