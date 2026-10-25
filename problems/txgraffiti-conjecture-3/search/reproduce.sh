#!/bin/sh
# Reproduce the searches summarised in search_summary.txt.
#   sh reproduce.sh [stage ...]      default stages: g48 xcheck quartic quintic sextic families
#                                    wblow blowup products sa
#   stages also available: quartic17 (n = 17, about 2 CPU-hours; JOBS parallel slices)
# Needs cc and nauty's geng on PATH; the Python stages need python3 with networkx, python-sat
# and ortools (set PY to choose the interpreter).  Binaries and logs go to $BUILD.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
BUILD=${BUILD:-/tmp/txgraffiti3-build}
PY=${PY:-python3}
JOBS=${JOBS:-3}
mkdir -p "$BUILD"
for p in tx3check transform wblow; do cc -O2 -o "$BUILD/$p" "$HERE/$p.c"; done
cc -O2 -o "$BUILD/sa_balanced_cnf" "$HERE/sa_balanced_cnf.c" -lm
"$PY" "$HERE/../certificates/g48_cnf.py" --g6 > "$BUILD/g48.g6"

# log a line "label SUMMARY ... secs=..." for the graph6 stream produced by the command "$@"
check() {
  label=$1; shift
  start=$(date +%s)
  "$@" | "$BUILD/tx3check" > "$BUILD/$label.out" 2> "$BUILD/$label.err"
  echo "$label $(grep SUMMARY "$BUILD/$label.out") secs=$(( $(date +%s) - start ))"
}
# graph6 streams; geng -c -dR -DR: connected R-regular graphs, isomorph-free
reg() { geng -c -d"$1" -D"$1" -q "$2" ${3:-}; }
fam() { reg 3 "$2" | "$BUILD/transform" "$1"; }
wbl() { reg "$1" "$2" | "$BUILD/wblow" "$3" "$4"; }

stage_g48() { check g48 cat "$BUILD/g48.g6"; grep COUNTEREXAMPLE "$BUILD/g48.out" | cut -c1-30; }
stage_xcheck() {
  : > "$BUILD/small.g6"
  for r in 3 4 5 6; do for n in 6 7 8 9 10 11 12; do
    if [ $n -gt $r ] && [ $((r * n % 2)) -eq 0 ]; then reg $r $n >> "$BUILD/small.g6"; fi
  done; done
  "$BUILD/tx3check" -v < "$BUILD/small.g6" > "$BUILD/small_c.txt"
  (cd "$HERE" && "$PY" xcheck_c.py "$BUILD/small_c.txt" && "$PY" crosscheck.py 2000)
}
stage_quartic() { for n in 5 6 7 8 9 10 11 12 13 14 15 16; do check quartic_n$n reg 4 $n; done; }
stage_quartic17() {
  j=0
  while [ $j -lt "$JOBS" ]; do check quartic_n17_$j reg 4 17 $j/"$JOBS" & j=$((j + 1)); done
  wait
}
stage_quintic() { for n in 6 8 10 12 14; do check quintic_n$n reg 5 $n; done; }
stage_sextic() { for n in 7 8 9 10 11 12 13 14; do check sextic_n$n reg 6 $n; done; }
stage_families() {
  for n in 4 6 8 10 12 14 16 18 20; do
    for mode in line prism k3; do check fam_${mode}_n$n fam $mode $n; done
  done
}
stage_wblow() {
  for n in 6 8 10 12 14 16 18; do check wb_cubic${n}_r4 wbl 3 $n 4 2; done
  for n in 6 8 10 12 14 16 18; do check wb_cubic${n}_r5 wbl 3 $n 5 3; done
  for n in 8 9 10 11 12 13 14; do check wb_quartic${n}_r5 wbl 4 $n 5 2; done
  for n in 4 6 8 10 12 14; do check wb_cubic${n}_r6 wbl 3 $n 6 4; done
}
stage_blowup() { (cd "$HERE" && "$PY" check_blowup.py "$BUILD/g48.g6"); }
stage_products() { (cd "$HERE" && "$PY" prod_check.py 2,3 "$BUILD/g48.g6"); }
stage_sa() {
  for T in "0.3 0.01" "0.1 0.005" "0.05 0.002"; do "$BUILD/sa_balanced_cnf" 3 15 1000000 4 7 $T; done
  for v in 12 14 16 18 20; do "$BUILD/sa_balanced_cnf" 4 $v 2000000 4 11 0.3 0.01; done
}

[ $# -gt 0 ] || set -- g48 xcheck quartic quintic sextic families wblow blowup products sa
for s in "$@"; do echo "== stage $s"; "stage_$s"; done
