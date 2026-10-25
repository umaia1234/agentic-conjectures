#!/usr/bin/env bash
# Reproduce the computer searches for WOWII Conjecture 189 (see README.md).
#
# usage: bash reproduce.sh NAUTY_DIR [OUT_DIR]
#   NAUTY_DIR  unpacked and configured nauty 2.9.3 source tree
#              (https://pallini.di.uniroma1.it/nauty2_9_3.tar.gz, SHA-256
#              9fc4edae04f88a0f5883985be3b39cf7f898fd6cc96e96b9ee25452743cc1b5b;
#              tar xzf nauty2_9_3.tar.gz && cd nauty2_9_3 && ./configure)
#   OUT_DIR    binaries, graphs and logs (default: ./out)
# environment:
#   FULL_MAX    largest order of the unpruned search (default 10; README reports 11)
#   SIGMA_MAX   largest order of the sigma(G) <= 3 search (default 16; 2 in effect skips it)
#   SIGMA4_MAX  largest order of the sigma(G) <= 4 search (default 15; 2 in effect skips it)
#   JOBS        parallel res/mod pieces for the larger orders (default 4)
#
# Stage 1 builds hyp189, ind189 and geng189 (nauty's geng with the PRUNE hook prune189.c).
# Stage 2 sends every connected graph with 2 <= n <= FULL_MAX through hyp189 and ind189.
# Stage 3 runs the pruned search for sigma(G) <= 3 (orders 2..SIGMA_MAX), checks its graphs
# with hyp189, ind189 and certify.py, and compares the certificates with the committed ones.
# Stage 4 checks, for n <= 10, that plain geng yields the same sigma(G) <= 3 hypothesis graphs.
# Stages 5 and 6 do the same for the pruned search with SMAX=4 (orders 2..SIGMA4_MAX), which
# keeps every hypothesis graph with sigma(G) <= 4; its certificates are those with sigma(G) = 4.
set -euo pipefail

if [ "${1:-}" = "--piece" ]; then
  # internal: one res/mod piece of the search with SMAX=smax
  n=$2 flags=$3 mod=$4 r=$5 out=$6 smax=$7
  # shellcheck disable=SC2086
  SMAX=$smax "$out/geng189" $flags -q "$n" "$r/$mod" > "$out/sigma$smax/n${n}_${r}of${mod}.g6"
  exit 0
fi

NAUTY=$(cd "${1:?usage: bash reproduce.sh NAUTY_DIR [OUT_DIR]}" && pwd)
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${2:-$HERE/out}
mkdir -p "$OUT/full" "$OUT/sigma3" "$OUT/sigma4"
OUT=$(cd "$OUT" && pwd)
FULL_MAX=${FULL_MAX:-10}
SIGMA_MAX=${SIGMA_MAX:-16}
SIGMA4_MAX=${SIGMA4_MAX:-15}
JOBS=${JOBS:-4}

echo "== stage 1: build"
cc -O3 -o "$OUT/hyp189" "$HERE/hyp189.c"
cc -O3 -o "$OUT/ind189" "$HERE/ind189.c"
make -C "$NAUTY" geng gtoolsW.o nautyW1.o nautilW1.o naugraphW1.o schreierW.o naurng.o \
  > "$OUT/make.log"
(cd "$NAUTY" && cc -O3 -DMAXN=WORDSIZE -DWORDSIZE=32 -DPRUNE=prune189 -I. \
  -o "$OUT/geng189" geng.c "$HERE/prune189.c" \
  gtoolsW.o nautyW1.o nautilW1.o naugraphW1.o schreierW.o naurng.o)

# first value of KEY=value in a summary file
field() { awk -v k="$2" '{for (i = 1; i <= NF; i++) if (index($i, k "=") == 1) {
  print substr($i, length(k) + 2); exit }}' "$1"; }

echo "== stage 2: every connected graph, 2 <= n <= $FULL_MAX"
for n in $(seq 2 "$FULL_MAX"); do
  rm -f "$OUT/full/fifo" && mkfifo "$OUT/full/fifo"
  "$OUT/ind189" < "$OUT/full/fifo" > "$OUT/full/ind_n$n.out" 2> "$OUT/full/ind_n$n.err" &
  pid=$!
  "$NAUTY/geng" -c -q "$n" | tee "$OUT/full/fifo" \
    | "$OUT/hyp189" > "$OUT/full/hyp_n$n.out" 2> "$OUT/full/hyp_n$n.err"
  wait "$pid"
  h=$(field "$OUT/full/hyp_n$n.err" hyp)
  i=$(field "$OUT/full/ind_n$n.err" hyp)
  echo "n=$n connected=$(field "$OUT/full/hyp_n$n.err" connected) hyp=$h ind_hyp=$i" \
    "CE=$(field "$OUT/full/hyp_n$n.err" CE) UNK=$(field "$OUT/full/hyp_n$n.err" UNK)" \
    "ind_nontraceable=$(field "$OUT/full/ind_n$n.err" nontraceable)"
  [ "$h" = "$i" ] && [ ! -s "$OUT/full/hyp_n$n.out" ] && [ ! -s "$OUT/full/ind_n$n.out" ] \
    || { echo "MISMATCH or counterexample at n=$n"; exit 1; }
done

rm -f "$OUT/full/fifo"

echo "== stage 3: sigma(G) <= 3, 2 <= n <= $SIGMA_MAX"
: > "$OUT/sigma3/certificates.txt"
for n in $(seq 2 "$SIGMA_MAX"); do
  # search_reduction (Lean): minimum degree >= n - 13 when sigma(G) <= 3
  flags=-c
  if [ "$n" -ge 15 ]; then flags="-c -d$((n - 13))"; fi
  mod=1
  if [ "$n" -ge 14 ]; then mod=$((JOBS * 16)); fi
  if [ "$n" -ge 16 ]; then mod=256; fi
  seq 0 $((mod - 1)) | xargs -P "$JOBS" -I{} bash "$0" --piece "$n" "$flags" "$mod" {} "$OUT" 3
  cat "$OUT"/sigma3/n"${n}"_*of"${mod}".g6 > "$OUT/sigma3/n$n.g6"
  "$OUT/hyp189" < "$OUT/sigma3/n$n.g6" > "$OUT/sigma3/hyp_n$n.out" 2> "$OUT/sigma3/hyp_n$n.err"
  "$OUT/ind189" < "$OUT/sigma3/n$n.g6" > "$OUT/sigma3/ind_n$n.out" 2> "$OUT/sigma3/ind_n$n.err"
  python3 "$HERE/certify.py" --make < "$OUT/sigma3/n$n.g6" > "$OUT/sigma3/cert_n$n.txt"
  c=$(wc -l < "$OUT/sigma3/cert_n$n.txt" | tr -d ' ')
  { echo "# n=$n count=$c"; cat "$OUT/sigma3/cert_n$n.txt"; } >> "$OUT/sigma3/certificates.txt"
  h=$(field "$OUT/sigma3/hyp_n$n.err" hyp)
  i=$(field "$OUT/sigma3/ind_n$n.err" hyp)
  echo "n=$n graphs=$(wc -l < "$OUT/sigma3/n$n.g6" | tr -d ' ') hyp=$h ind_hyp=$i" \
    "certified=$c CE=$(field "$OUT/sigma3/hyp_n$n.err" CE)"
  [ "$h" = "$i" ] && [ "$h" = "$c" ] && [ ! -s "$OUT/sigma3/hyp_n$n.out" ] \
    && [ ! -s "$OUT/sigma3/ind_n$n.out" ] || { echo "MISMATCH or counterexample at n=$n"; exit 1; }
done
m=$(( SIGMA_MAX < 10 ? SIGMA_MAX : 10 ))
echo "== stage 4: plain geng gives the same sigma(G) <= 3 hypothesis graphs, 2 <= n <= $m"
for n in $(seq 2 "$m"); do
  "$NAUTY/geng" -c -q "$n" | "$OUT/hyp189" -dump 2> /dev/null \
    | awk '$2 == 1 && $5 == 1 && $3 <= 3 {print $1}' | sort > "$OUT/sigma3/plain_n$n.txt"
  cut -d' ' -f1 "$OUT/sigma3/cert_n$n.txt" | sort | cmp -s - "$OUT/sigma3/plain_n$n.txt" \
    || { echo "different sigma(G) <= 3 graphs at n=$n"; exit 1; }
  echo "n=$n same set, size $(wc -l < "$OUT/sigma3/plain_n$n.txt" | tr -d ' ')"
done
if [ "$SIGMA_MAX" -eq 16 ]; then
  python3 "$HERE/certify.py" "$OUT/sigma3/certificates.txt"
  diff <(grep -v '^#' "$HERE/sigma3_certificates.txt" | cut -d' ' -f1 | sort) \
    <(grep -v '^#' "$OUT/sigma3/certificates.txt" | cut -d' ' -f1 | sort) \
    && echo "same graphs as the committed sigma3_certificates.txt"
fi

echo "== stage 5: sigma(G) <= 4, 2 <= n <= $SIGMA4_MAX"
: > "$OUT/sigma4/certificates.txt"
for n in $(seq 2 "$SIGMA4_MAX"); do
  # search_reduction_four (Lean): minimum degree >= n - 11 when sigma(G) <= 4
  flags=-c
  if [ "$n" -ge 15 ]; then flags="-c -d$((n - 11))"; fi
  mod=1
  if [ "$n" -ge 13 ]; then mod=$((JOBS * 16)); fi
  seq 0 $((mod - 1)) | xargs -P "$JOBS" -I{} bash "$0" --piece "$n" "$flags" "$mod" {} "$OUT" 4
  cat "$OUT"/sigma4/n"${n}"_*of"${mod}".g6 > "$OUT/sigma4/n$n.g6"
  "$OUT/hyp189" < "$OUT/sigma4/n$n.g6" > "$OUT/sigma4/hyp_n$n.out" 2> "$OUT/sigma4/hyp_n$n.err"
  "$OUT/ind189" < "$OUT/sigma4/n$n.g6" > "$OUT/sigma4/ind_n$n.out" 2> "$OUT/sigma4/ind_n$n.err"
  python3 "$HERE/certify.py" --sigma4 --make < "$OUT/sigma4/n$n.g6" > "$OUT/sigma4/cert_n$n.txt"
  c=$(wc -l < "$OUT/sigma4/cert_n$n.txt" | tr -d ' ')
  { echo "# n=$n count=$c"; cat "$OUT/sigma4/cert_n$n.txt"; } >> "$OUT/sigma4/certificates.txt"
  h=$(field "$OUT/sigma4/hyp_n$n.err" hyp)
  i=$(field "$OUT/sigma4/ind_n$n.err" hyp)
  # hypothesis graphs with sigma(G) = 4, as counted by each program
  h4=$(awk '$1 == "hyp" && $2 == "sigma=4:" {print $3}' "$OUT/sigma4/hyp_n$n.err")
  i4=$(awk '$1 == "sigma=4" {print substr($2, 5)}' "$OUT/sigma4/ind_n$n.err")
  echo "n=$n graphs=$(wc -l < "$OUT/sigma4/n$n.g6" | tr -d ' ') hyp=$h ind_hyp=$i" \
    "sigma4_hyp=${h4:-0} sigma4_ind_hyp=${i4:-0} certified=$c" \
    "CE=$(field "$OUT/sigma4/hyp_n$n.err" CE)"
  [ "$h" = "$i" ] && [ "${h4:-0}" = "${i4:-0}" ] && [ "${h4:-0}" = "$c" ] \
    && [ ! -s "$OUT/sigma4/hyp_n$n.out" ] && [ ! -s "$OUT/sigma4/ind_n$n.out" ] \
    || { echo "MISMATCH or counterexample at n=$n"; exit 1; }
done
m=$(( SIGMA4_MAX < 10 ? SIGMA4_MAX : 10 ))
echo "== stage 6: plain geng gives the same sigma(G) = 4 hypothesis graphs, 2 <= n <= $m"
for n in $(seq 2 "$m"); do
  "$NAUTY/geng" -c -q "$n" | "$OUT/hyp189" -dump 2> /dev/null \
    | awk '$2 == 1 && $5 == 1 && $3 == 4 {print $1}' | sort > "$OUT/sigma4/plain_n$n.txt"
  cut -d' ' -f1 "$OUT/sigma4/cert_n$n.txt" | sort | cmp -s - "$OUT/sigma4/plain_n$n.txt" \
    || { echo "different sigma(G) = 4 graphs at n=$n"; exit 1; }
  echo "n=$n same set, size $(wc -l < "$OUT/sigma4/plain_n$n.txt" | tr -d ' ')"
done
if [ "$SIGMA4_MAX" -eq 15 ]; then
  python3 "$HERE/certify.py" --sigma4 "$OUT/sigma4/certificates.txt"
  diff <(grep -v '^#' "$HERE/sigma4_certificates.txt" | cut -d' ' -f1 | sort) \
    <(grep -v '^#' "$OUT/sigma4/certificates.txt" | cut -d' ' -f1 | sort) \
    && echo "same graphs as the committed sigma4_certificates.txt"
fi
echo "== done"
