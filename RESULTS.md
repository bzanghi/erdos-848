# Erdős #848 — verification record (2026-10-12)

| Range | Method | Result | Evidence |
|---|---|---|---|
| 1 ≤ N ≤ 10⁴ | exact max clique (`maxclique_small.c`) | ω(G_N) = M(N) for every N | `small10k.txt` |
| 1 ≤ N ≤ 5000 | independent Bron–Kerbosch (`bk_check.py`) | 0 mismatches | console run |
| 9982 ≤ N ≤ 10⁹ | colouring certificate (`dyn_colour.c`, seed 1) | SUCCESS: 105,158,686 vertices, 13,806,588 augmenting moves | `results/run_1e9.out`, `results/log_1e9.bin` (676 MB) |
| 9982 ≤ N ≤ 10⁹ | independent replay (`verify_log.c`: trial division to the cube root, different √−1 algorithm) | VERIFIED: 121,112,532 pairs, 0 bad, |B| matches | console run, 2m16s on 14 threads |
| 9982 ≤ N ≤ 10⁸ | same, separate seed-1 run | VERIFIED: 12,110,287 pairs, 0 bad | `results/log_1e8.bin` |
| 1 ≤ n ≤ 10⁹ | PARI/GP recount of the vertex set (`uissquarefree(n²+1)`) | count 105,158,686 and the sum/sum-of-squares hash both match the verifier | `results/pari_B_summary.txt` |
| verifier sanity | tampered logs | both rejected (adjacent pairs; a vertex never added) | `results/tamper{1,2}.bin` |
| 5·10⁸ ≤ N ≤ 10³⁵ | explicit bounds, 180-interval grid (`grid_check.py`) | ALL OK, worst UB/(M+1) = 0.9960 on [5e8, 7e8] | `results/grid_5e8_1e35.txt` |
| 5·10⁸ ≤ N ≤ 10³⁵ | same bounds in Arb interval arithmetic + exact rationals (`analytic_rig.py grid`) | ALL OK, 181 intervals, worst 0.996034 | `results/grid_rig_5e8_1e35.txt` |
| N ≥ 10³⁵ | rigorous tail (`analytic_rig.py tail`) | 25·(U_lin + S/N) ≤ 0.748362 < 1 | console run |
| 9982 ≤ N ≤ 10⁹ | PARI/GP `uissquarefree` re-check of every certificate pair | 121,112,532 pairs, 0 non-squarefree | `results/pari_pairs_summary.txt` |
| N ≥ 10³⁵ | monotone tail bound | 25·(U_lin + S/N) = 0.748 < 1 | `results/grid_5e8_1e35.txt`, first line |
| §3 logic | independent adversarial review + re-implementation, without seeing `analytic_check.py` | no fatal gaps; 4 fixable/2 cosmetic items fixed in NOTE.md; independent UB/M ≤ 0.763 on [5e8, 1e13]; lemma spot-checks all hold | `review/` |

Conclusion: for every N ≥ 1, the maximum size of A ⊆ [1,N] with ab+1 non-squarefree for all a, b ∈ A (a = b
allowed) is #{n ≤ N : n ≡ 7 mod 25}, attained by that residue class.

Not yet done: human expert review; Lean formalisation; posting to erdosproblems.com (outward-facing, needs Ben's OK).
Reproduce: `./maxclique_small 10000`; `./dyn_colour 1000000000 9982 1 log.bin && ./verify_log 1000000000 9982 log.bin 14`
(about 1 h + 2 min); `python grid_check.py 5e8 1e35` (about 25 min). Build with
`clang -O3 -isysroot /Library/Developer/CommandLineTools/SDKs/MacOSX26.5.sdk` (the default SDK 27 linker is broken on this machine).
