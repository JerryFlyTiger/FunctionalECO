#!/bin/bash
# run_all.sh -- run ./eco on every testcase, time it, then independently verify
# and score each patch with evaluate.py. Prints a summary table vs beta rank-1.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ECO="${ECO:-$ROOT/eco/build/eco}"
EVAL="$ROOT/evaluator/evaluate.py"
TC="$ROOT/testcase"
OUT="${OUT:-$ROOT/out}"
mkdir -p "$OUT"

# beta rank-1 targets (test01..test10; 09/10 numbering vs our hidden set uncertain)
rank1() {
  case "$1" in
    test01) echo 5;; test02) echo 32;; test03) echo 163;; test04) echo 1;;
    test05) echo 12;; test06) echo 72;; test07) echo 73;; test08) echo 235;;
    test09) echo 10;; test10) echo 20;; *) echo "-";;
  esac
}

printf "%-8s %8s %8s %8s %10s  %s\n" "case" "cost" "rank1" "time(s)" "verdict" "note"
total_fail=0
for d in "$TC"/test0* "$TC/hidden cases"/test*; do
  [ -d "$d" ] || continue
  n=$(basename "$d")
  patch="$OUT/patch_$n.v"
  t0=$(python3 -c 'import time; print(time.time())')
  "$ECO" "$d/g1.v" "$d/r2.v" "$patch" > "$OUT/eco_$n.log" 2>&1
  rc=$?
  t1=$(python3 -c 'import time; print(time.time())')
  dt=$(python3 -c "print(f'{$t1-$t0:.2f}')")
  if [ $rc -ne 0 ]; then
    printf "%-8s %8s %8s %8s %10s  %s\n" "$n" "-" "$(rank1 "$n")" "$dt" "ECO_FAIL" "rc=$rc"
    total_fail=$((total_fail+1)); continue
  fi
  res=$(python3 "$EVAL" "$d/g1.v" "$d/r2.v" "$patch" 2>&1)
  if [[ "$res" == PASS* ]]; then
    cost=${res#PASS cost=}
    r1=$(rank1 "$n")
    note=""
    if [[ "$r1" != "-" ]]; then
      if (( cost < r1 )); then note="BEAT rank1"; elif (( cost == r1 )); then note="tie"; else note="behind by $((cost-r1))"; fi
    fi
    printf "%-8s %8s %8s %8s %10s  %s\n" "$n" "$cost" "$r1" "$dt" "PASS" "$note"
  else
    printf "%-8s %8s %8s %8s %10s  %s\n" "$n" "-" "$(rank1 "$n")" "$dt" "VERIFY_FAIL" "$res"
    total_fail=$((total_fail+1))
  fi
done
echo
if [ $total_fail -eq 0 ]; then echo "ALL PASS"; else echo "$total_fail case(s) FAILED"; exit 1; fi
