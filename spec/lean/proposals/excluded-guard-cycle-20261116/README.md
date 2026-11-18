# Real-exclusion counterexample to actual uniform coverage

Synthetic, fully analyzed acyclic code plus four literal marking rules.
No cleaner, pass rule, recursion, loop or unresolved-library model.
Production is unchanged. Follow [proof-guide.md](../../../proof-guide.md).

[Code, complete annotated runs, root cause and limits](../../../../docs/reports/bidirectional-excluded-guard-nontermination-20261116.md).

The selected reference enables NE, raw C5, qualified demand heads, bounded
plans, strict saved MUST and the latest actual NORMAL uniform coverage.
An ordinary write creates `a.f.MUST/T {g},N`. A coarse first-field STAR
query still produces root MAY. Precise replies are confined to h and cannot
cover the whole root question. Three calls share the same method owner.

The exact cold execution reaches **run-7/run-8** states F and B. For all
n>=0, history(2n+7)=F and history(2n+8)=B. They retain 52 and 58 qualified
DEMAND rows, respectively, and the root Target never closes. The finite
native diagnostic completes **run-31** at its policy limit. It is not the
uncapped proof.

| Module | Checked scope |
|---|---|
| Excluded | Complete marked-return/control fragment: native-shaped E-aware conditional GEN, real nested replacement, original C2 and qualified plan, raw paired C5/cuts, current/saved matching, NORMAL persistence, actual coverage and accumulated Target controls. |
| Kernel | Principal native cells: real hole, coarse/fine starts, guarded GEN, actual binding, child non-coverage, reverse broad demand and ZERO/Target route. |
| Phase | Generic equality for any later run with the same direction and budget. No finite run horizon. |
| Frozen | Literal F/B witnesses. Definitions are not correctness assumptions. |
| Cold | Every run-1..run-8 next-state equality, persistence and worklist quiescence; constructive reachability from the actual initial state. |
| ParametricRounds | Every steady delivery/publication step for arbitrary budget n+4; exact factoring of the ordinary sweep; accumulated Target. |
| Steady | Parametric steps and the actual unbounded field-limit schedule. |
| Recurrence | Uncapped exact two-state induction, repeated demand membership, nonempty frontier, live Target, and parametric quiescence. |
| KernelEval | Proof-runner helper only: close local parameters around the ordinary `of_decide_eq_true rfl` certificate and submit it to Lean's trusted kernel. No analyzer change or external decision oracle. |

**161 new constructive claims; 3,884 audited claims in 179 modules.** Only
`propext` and `Quot.sound` are permitted. No custom axioms, holes or classical
choice. The proof-runner helper emits ordinary proof terms; the independent
axiom audit follows their generated auxiliary declarations too.

```bash
python3 spec/lean/proposals/excluded-guard-cycle-20261116/check.py \
  --out /tmp/excluded-guard-proofs
```

`--dependencies DIR` reuses a completed uniform-coverage dependency build,
with every source hash checked. The new modules are compiled and audited.
All frozen equalities and all budget-parametric facts are kernel checked.
The arbitrary n in the final induction is not an exporter limit.

Two native tests pass in `ExcludedGuardCycleTest`. They check the unmodified
engine's finite behavior and the exact ordinary-write/C2/GEN/coverage cells.
They do not claim an integrated native NE run or a whole-engine bisimulation.
Unchanged argument/ZERO identities are outside the marked-return fragment.
Their existing service cannot provide a missing fresh cross-mark root mark.

Diagnostic exporters and the readable trace renderer are in
[scripts/demand_experiments/excluded-guard-cycle-20261116](../../../../scripts/demand_experiments/excluded-guard-cycle-20261116).
Bulk data and compiled output remain in the external report-data archive.
