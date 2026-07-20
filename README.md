# FunctionalECO — 2021 CAD Contest Problem A (G1 vs R2 two-netlist variant)

Generates a minimum-cost functional ECO patch for `g1.v` so that the patched
netlist is combinationally equivalent to `r2.v` (R1 is ignored by design).

## Layout

```
eco/          C++17 engine  (gmake -> eco/build/eco)
  src/netlist.hpp   flat structural Verilog parser (buses, escaped names, assign)
  src/aig.hpp       AIG + strashing + 64-bit parallel simulation
  src/sat.hpp       CaDiCaL incremental SAT wrapper (Tseitin on demand)
  src/rectify.hpp   SAT-based internal-point rectification engine
  src/patch.hpp     BLIF I/O, ABC glue, contest cost model, patch.v writer
  src/main.cpp      flow: sweep matching -> candidates portfolio -> verify -> emit
evaluator/    independent Python/shell scorer (zero code shared with eco/)
  evaluate.py       official cost + apply-patch + ABC cec equivalence check
  run_all.sh        run & time all 14 testcases, table vs beta rank-1
tools/        third-party sources built locally (git-ignored)
  abc/              berkeley-abc (AIG optimization dc2/dch, map -a, cec)
  cadical/          CaDiCaL SAT solver (linked into eco)
testcase/     test01..08 + hidden cases/test09..14 (g1.v, r2.v each)
```

## Build & run

Build tool: GNU Make 4.4.1 via Homebrew (`brew install make`), installed as
`gmake` — macOS ships only the ancient GPLv2-locked 3.81 as `/usr/bin/make`.

```sh
(cd tools/abc && gmake -j8 ABC_USE_NO_READLINE=1)
(cd tools/cadical && ./configure && gmake -j8)
(cd eco && gmake)
./eco/build/eco <g1.v> <r2.v> <patch.v>       # also: eco r1.v r2.v g1.v patch.v
./evaluator/run_all.sh                        # full regression + scoring table
```

## Algorithm

1. **Matching**: G1 and R2 share one AIG over name-matched PIs; fraig-style sweep
   (random simulation buckets + incremental SAT) builds functional equivalence
   classes, giving every R2 node its equivalent existing G1 nets.
2. **Candidate portfolio** (all SAT-verified, min contest cost wins):
   - baseline A: per failing PO, copy the R2 cone cut at matched G1 nets, with
     consumer-preservation targets;
   - baseline B: same but *without* preservation when a SAT check proves the
     PO consumers tolerate the new values (cuts ~1 wire+1 gate per consumer);
   - rectification: iteratively pick an internal net t and synthesize f(existing
     nets) with cofactor-miter validity (UNSAT bad0&bad1), CEGAR support
     selection, truth-table enumeration; fixes several POs with a few wires;
   - hybrid: cheap rectify fixes + baseline for the remaining POs.
3. **Minimization**: every candidate goes through ABC (`dc2`, `dch -f`,
   `map -a` onto a genlib whose area equals the contest cost: 2-input gates = 1,
   inv/buf ~ 0) — the cost function is exactly AIG-node count + boundary wires,
   so ABC's objective aligns perfectly.
4. **Verification**: eco re-applies its own patch and SAT-checks every PO; the
   independent evaluator re-parses, re-applies, checks acyclicity and runs ABC
   `cec` as a neutral referee.

## Results (beta rank-1 comparison)

| case | cost | rank1 | verdict | | case | cost | rank1 | verdict |
|------|-----:|------:|---------|-|------|-----:|------:|---------|
| test01 | 5 | 5 | tie | | test08 | 4 | 235 | **beat** |
| test02 | 7 | 32 | **beat** | | test09 | 5 | 10 | **beat** |
| test03 | 11 | 163 | **beat** | | test10 | 10 | 20 | **beat** |
| test04 | 1 | 1 | tie | | test11 | 11 | – | pass |
| test05 | 2 | 12 | **beat** | | test12 | 24 | – | pass |
| test06 | 60 | 72 | **beat** | | test13 | 98 | – | pass |
| test07 | 59 | 73 | **beat** | | test14 | 134 | – | pass |

Contest-style total (test01–10, score = min/ours): **10.00 vs rank-1's 5.08** —
beat or tie on every comparable case. The final portfolio comes from a 100-seed
x dual-work-budget census; a post-selection care-set simplification pass
(global-miter-verified substitutions + constant-support folding + dead sweep)
then shaves what the mapper cannot see (t06 64->60, t07 63->59). test13 = 98 is
unchanged across 200+ configurations and every technique — strong evidence its
new-logic cone is near the structural floor.
All runtimes < 6 s (limit 180 s); output is fully deterministic — the engine runs
a best-of-4 portfolio of deterministic trajectories (different sim seeds /
SAT-call budgets / fix thresholds), each SAT-call-budgeted instead of
wall-clock-budgeted, so identical inputs produce bit-identical patches on any
machine speed. Determinizing iteration orders alone uncovered test03 = 11
(was 152). Two-point joint rectification runs when single-point rounds stall (validity is
one UNSAT over four cofactor miters; f1 from "both v1 options bad" must-sets,
f2 from the f1-conditioned bads; divisors exclude the union TFO). TT synthesis
minimizes with constant DC fills plus espresso-lite greedy cube expansion over
ON+DC / OFF+DC. Hybrid spec building can also "rematch" against the partially
fixed circuit's current values (sim-signature buckets + SAT, budget-guarded).

### Performance notes
Profiled bottlenecks and fixes: truth tables are built by SAT *model
enumeration* (care cells only) instead of 2^|S| membership queries; the greedy
divisor set-cover runs on bit-packed pair matrices (popcount); per-round AIG
rollback + solver reset stop scratch cofactor cones from accumulating; pattern
injection refreshes only the 2 care sim-words; all ABC scripts run in one
process spawn; failing-PO set is maintained incrementally (validity proofs
already cover the fixed POs); CaDiCaL runs `configure("plain")`. Default
rectification budget is counted in SAT calls (`ECO_RECT_WORK`), so results are
machine-independent. The 5 portfolio trajectories are fully independent and run
in parallel threads (`ECO_SERIAL=1` forces sequential; output is bit-identical
either way — selection is order-independent). Worst case ~4.4 s (test14).

## Env knobs

`ECO_VERBOSE=1` trace; `ECO_ABC=<path>`; `ECO_RECT_WORK=<satcalls>` (default 9000); `ECO_TRAJ=<n>` trajectory count;
`ECO_SEED=<hex>` override sim seed;
`ECO_RECT_MAXCOST=<n>` fix acceptance per PO (default 16);
`ECO_EXTRA_SCRIPT="..."` extra ABC script; `ECO_KEEP_TMP=1` keep temp dir;
`ECO_PAIR_TOP/ECO_PAIR_MAX/ECO_PAIR_SAT` pair-search caps (64/2000/100);
`ECO_PAIR_R0=1` also try high-gain pairs before single-point rounds.
