#!/usr/bin/env bash
set -euo pipefail

find_nauty_tool() {
    if command -v "$1" >/dev/null 2>&1; then
        command -v "$1"
    elif command -v "nauty-$1" >/dev/null 2>&1; then
        command -v "nauty-$1"
    else
        echo "missing nauty tool: $1 (or nauty-$1)" >&2
        exit 1
    fi
}

GENG=${GENG:-$(find_nauty_tool geng)}
DIRECTG=${DIRECTG:-$(find_nauty_tool directg)}
CXX=${CXX:-c++}
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

"$CXX" -O3 -std=c++17 -Wall -Wextra -pedantic \
    "$HERE/pulse_analyze.cpp" -o "$HERE/pulse_analyze"
"$CXX" -O3 -std=c++17 -Wall -Wextra -pedantic \
    "$HERE/pulse_analyze_kahn.cpp" -o "$HERE/pulse_analyze_kahn"

for n in 1 2 3 4 5 6; do
    echo "n=$n"
    "$GENG" -q "$n" | "$DIRECTG" -q -T | "$HERE/pulse_analyze" "$n"
done

echo "independent n=6 upper-bound check"
"$GENG" -q 6 | "$DIRECTG" -q -T | "$HERE/pulse_analyze_kahn" 6

python3 "$HERE/verify_witness.py"
