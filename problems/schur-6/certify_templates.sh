#!/usr/bin/env bash
# Re-certify the template classes at n = 538 reported as certified in README.md.
#
# For each class: regenerate the CNF with template_sat.py, check its SHA-256
# and audit every clause with audit_template_cnf.py, then (unless
# --audit-only) solve it with kissat writing a DRAT proof and check the proof
# with drat-trim.  Proofs are large (0.07-2.3 GB) and are deleted after the
# check.  Usage: bash certify_templates.sh [--audit-only] [NAME ...]
# (NAMEs restrict the run to the listed classes, e.g. g151_38).
set -euo pipefail
cd "$(dirname "$0")"
audit_only=0
if [ "${1:-}" = "--audit-only" ]; then
  audit_only=1
  shift
fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# name | template_sat.py / audit_template_cnf.py class arguments | CNF SHA-256
#      | extra kissat options
classes=(
  "g148_37|--maximum 538 --palindromic --frame 148 37|30f8862da0b42ce3f19dc3e42bad6d93829c8524619eb001aa567613a8a44334|--sat"
  "g149_37|--maximum 538 --palindromic --frame 149 37|68754c62d18e1734b5b2a82e61186ec359b604018e986814395ad50f6ac9f450|--sat"
  "g150_37|--maximum 538 --palindromic --frame 150 37|3b6b04609be5878d4c2dbcf31047952a727b2268d01160c55681013f0234dd68|--sat"
  "g151_37|--maximum 538 --palindromic --frame 151 37|702e7d3c33628cd97139e1209c4bff60ddb1eec684fbb3a667e4e43c95744f11|--sat"
  "g152_37|--maximum 538 --palindromic --frame 152 37|6a0655e499c5ae4955b9957f40f24d0bf57e58565eaa5e700f26190a84751ca9|--sat"
  "g153_37|--maximum 538 --palindromic --frame 153 37|54f22cd411ce96a7e65fb58e84e5222c89b763bbf00710a8db2fe5032f767139|--sat"
  "g154_37|--maximum 538 --palindromic --frame 154 37|0021968ebc1d353dfa218a212e9418537597a0f8a90407f88ae0bccd105c1323|--sat"
  "g148_38|--maximum 538 --palindromic --frame 148 38|b1e24788b7009bd04bd0dba468374c7542cd5f1f86ee5a7c40c48d7b4a85bebb|"
  "g149_38|--maximum 538 --palindromic --frame 149 38|ad9ee92eb97c11e166d72fd40378765155337a4d8c41257788a42b4eb0bdbda3|"
  "g150_38|--maximum 538 --palindromic --frame 150 38|9dcfec4ae5f737596b44b8230db0af24b1814755a55327930fae465362ff2076|"
  "g151_38|--maximum 538 --palindromic --frame 151 38|3be571b5b80901eb581e6ed42fa230ca427ccdb62dec311665366d43b8548643|"
  "g152_38|--maximum 538 --palindromic --frame 152 38|68ba61b0908840d72e662a51ef233d57f12d592ee939802d2f1f6162629cabf1|"
  "g153_38|--maximum 538 --palindromic --frame 153 38|39b4f540f80bc9fde6a1abe0ed4ee34e6a485bf58851a8a2e9da7652203eca0e|"
  "g154_38|--maximum 538 --palindromic --frame 154 38|aaa28f3830f42976498ede1d3309dd2212c0eb317d00f466972280010e1496e4|"
  "g148_39|--maximum 538 --palindromic --frame 148 39|189fef22cdb642fdafa471317e137c715ecbce7af22d07b0521d69cc993774df|"
  "g149_39|--maximum 538 --palindromic --frame 149 39|39929b63e17f637c8f687dcef6de5cce4415e5d58a085fc44507b8433a7f6cdd|"
  "g150_39|--maximum 538 --palindromic --frame 150 39|65e5c529ca66b61eea0d8ef9b0cbd2c8fff341e67259b795bce51b35826bfafb|"
  "g151_39|--maximum 538 --palindromic --frame 151 39|bf639be3cb11962ae4ae810005fc3e07eb42b2d6bf358843254ddc0f0c4a72a0|"
  "g152_39|--maximum 538 --palindromic --frame 152 39|ed8b1023ff44b1d0c326294d186583e347a8255ea98d7ceaa2e3167a88e30b2c|"
  "g153_39|--maximum 538 --palindromic --frame 153 39|661c9a293998c42b5e0a205cf33d1018f0ff5b8fa6bf4a9b81a1795d9d7b2a67|"
  "g154_39|--maximum 538 --palindromic --frame 154 39|e3ea6c4ceadeab80f5001fc3d63aa1d02a3dae15166090ce79f5da93daaa687c|"
  "g151_38_nomid|--maximum 538 --palindromic --frame 151 38 --no-middle|d21429f362c72dec511036cb389cb7e7dea979633ef4f3adb14928a73fb1313f|"
  "prefix120|--maximum 538 --fix published_537.col 120|ef261df813a4f9d6b4254cc7fa8d20d1790bd23b97c1dbf642cb958d8db68ee1|"
)

for entry in "${classes[@]}"; do
  IFS='|' read -r name args sha kopts <<< "$entry"
  if [ "$#" -gt 0 ] && [[ " $* " != *" $name "* ]]; then
    continue
  fi
  cnf="$work/$name.cnf"
  # shellcheck disable=SC2086
  python3 template_sat.py cnf $args > "$cnf"
  # shellcheck disable=SC2086
  python3 audit_template_cnf.py "$cnf" $args --sha256 "$sha"
  if [ "$audit_only" -eq 1 ]; then
    continue
  fi
  status=0
  # shellcheck disable=SC2086
  kissat -q $kopts "$cnf" "$work/$name.drat" > "$work/$name.out" || status=$?
  if [ "$status" -ne 20 ]; then
    echo "$name: kissat exit $status (expected 20 = UNSAT)"
    exit 1
  fi
  result=$(drat-trim "$cnf" "$work/$name.drat" -t 40000 | tr '\r' '\n' | grep -E '^s ' || true)
  rm -f "$work/$name.drat"
  if [ "$result" != "s VERIFIED" ]; then
    echo "$name: drat-trim did not verify the proof (${result:-no status line})"
    exit 1
  fi
  echo "$name: certified UNSAT"
done
