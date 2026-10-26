#!/bin/sh
# Print the canonical graph6 string of every connected graph on N vertices with gamma_t >= K,
# for the search of small counterexamples to WOWII Conjecture 300 (a violation on N vertices
# needs 2*gamma_t >= N + 2).
#
# Usage: sh closure_wowii300.sh N K [SWEEP]
#   N <= 62, 2K >= N; SWEEP is the compiled sweep_wowii300.c (default build/sweep_wowii300).
#   Needs gentreeg, addedgeg and labelg from nauty.
#
# Method. If H is a spanning subgraph of G without isolated vertices, every total dominating
# set of H is one of G, so gamma_t(H) >= gamma_t(G). A connected G with gamma_t(G) >= K
# therefore has a spanning tree T with gamma_t(T) >= K, and adding the edges of G - T to T one
# at a time passes only through graphs with gamma_t >= K. So the script starts from the trees
# with gamma_t >= K and adds one edge in every possible way, keeping the graphs with
# gamma_t >= K, until no graph is left; labelg and sort -u remove isomorphic copies. The
# gamma_t filter reads the NEAR lines of SWEEP -p, which cover every graph with
# 2*gamma_t >= N, hence the condition 2K >= N.
n=$1
k=$2
sweep=${3:-build/sweep_wowii300}
if [ -z "$n" ] || [ -z "$k" ] || [ $((2 * k)) -lt "$n" ]; then
    echo "usage: sh closure_wowii300.sh N K [SWEEP], with 2K >= N" >&2
    exit 2
fi
filter() { "$sweep" -p | awk -F'[ =]' -v k="$k" '$1 == "NEAR" && $6 >= k { print $2 }'; }
level=$(gentreeg -q "$n" | labelg -qg | sort -u | filter)
while [ -n "$level" ]; do
    printf '%s\n' "$level"
    level=$(printf '%s\n' "$level" | addedgeg -q | labelg -qg | sort -u | filter)
done
