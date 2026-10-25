#!/bin/sh
# Regenerate the committed DRAT certificate rds143_core.cnf + rds143_core.drat for
# "there is no (13,11,12,1) relative difference set in Z_143" (README, part 2).
# Needs python3, cadical (tested with 3.0.1) and drat-trim; intermediate files go to
# build/.  Regenerated files need not be byte-identical with the committed ones.
set -eu
cd "$(dirname "$0")"
mkdir -p build
# full formula (normalised sets, ratio clauses up to R = 6)
python3 ds_cnf.py 143 12 13 build/rds143_full.cnf 6
cadical -q --no-binary build/rds143_full.cnf build/rds143_full.drat || test $? -eq 20
# keep only the clauses used by the refutation, then refute that core again
drat-trim build/rds143_full.cnf build/rds143_full.drat -c rds143_core.cnf
cadical -q --no-binary --unsat rds143_core.cnf build/rds143_core_raw.drat || test $? -eq 20
# keep only the lemmas used by the second refutation (-O: iterate to a fixpoint, ~8 min)
drat-trim rds143_core.cnf build/rds143_core_raw.drat -l rds143_core.drat -O
drat-trim rds143_core.cnf rds143_core.drat
python3 audit_ds_cnf.py 143 12 13 6 rds143_core.cnf
