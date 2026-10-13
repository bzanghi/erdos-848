#!/usr/bin/env bash
# Reproduce every computation for Erdős #848. Requirements: a C compiler, Python 3 with numpy and
# python-flint, PARI/GP (libpari headers), zstd. About 1.5 h on a 16-core machine.
set -euo pipefail
cd "$(dirname "$0")"
CC=${CC:-cc}; CFLAGS=${CFLAGS:-"-O3"}; PY=${PY:-python3}
mkdir -p build out
$CC $CFLAGS -o build/maxclique_small src/maxclique_small.c
$CC $CFLAGS -o build/dyn_colour src/dyn_colour.c
$CC $CFLAGS -o build/verify_log src/verify_log.c -lpthread
echo "== 1. exact clique numbers, N <= 10^4";  build/maxclique_small 10000 > out/small10k.txt; grep -c OK out/small10k.txt; ! grep DIFF out/small10k.txt
echo "== 1b. independent Bron-Kerbosch, N <= 5000"; $PY src/bk_check.py 5000
echo "== 2. colouring certificate 9982 <= N <= 10^9 (or use the released log: zstd -d log_1e9.bin.zst)"
[ -f out/log_1e9.bin ] || build/dyn_colour 1000000000 9982 1 out/log_1e9.bin
build/verify_log 1000000000 9982 out/log_1e9.bin 16 out/pairs_1e9.bin
echo "== 2b. PARI/GP cross-checks"
PARI_INC=${PARI_INC:-/opt/homebrew/include}; PARI_LIB=${PARI_LIB:-/opt/homebrew/lib}
$CC -O2 -I$PARI_INC -L$PARI_LIB -o build/pari_pairs pari/pari_pairs.c -lpari
$CC -O2 -I$PARI_INC -L$PARI_LIB -o build/pari_B pari/pari_B.c -lpari
NP=$(( $(stat -f%z out/pairs_1e9.bin 2>/dev/null || stat -c%s out/pairs_1e9.bin) / 16 ))
for i in $(seq 0 15); do build/pari_pairs out/pairs_1e9.bin $((NP*i/16)) $((NP*(i+1)/16)) > out/pp_$i.txt & done; wait
cat out/pp_*.txt | awk '{n+=$3; b+=$4} END {print "PARI pairs", n, "bad", b}'
for i in $(seq 0 15); do build/pari_B $((1000000000*i/16+1)) $((1000000000*(i+1)/16)) > out/pb_$i.txt & done; wait
cat out/pb_*.txt | awk '{c+=$3} END {print "PARI |B| up to 1e9 =", c}'
echo "== 3. analytic range in interval arithmetic"
(cd src && $PY analytic_rig.py tail 1e35 && $PY analytic_rig.py grid 5e8 1e35 | tail -1)
