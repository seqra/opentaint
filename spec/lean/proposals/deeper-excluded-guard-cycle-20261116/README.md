# Deeper real-exclusion counterexample

16 November 2026. Synthetic data-flow reachability. Follow
[proof-guide.md](../../../proof-guide.md). Production is unchanged.
[Code and proof explanation](../../../../docs/reports/bidirectional-deeper-excluded-guard-nontermination-20261116.md).
[Complete run-1 through run-10 annotations](../../../../docs/reports/bidirectional-deeper-excluded-guard-trace-20261116.md).

The latest carried-real-E admission repair is enabled. Source, guard and
write heads move one level deeper than the previous example. No loop,
recursion, cleaner, special pass rule, unresolved method or intrinsic-MAY
assignment is used. All transfers come from analyzed ordinary code and four
literal unary marking actions.

## Result

**160 new constructive claims; 4,502 audited declarations in 218 modules**,
Lean 4.35.0. Only `propext` and `Quot.sound` may occur in theorem axiom
closures. There is no custom axiom, hole, classical choice or external
evaluation oracle. Frozen values are executable witnesses whose transitions
are checked by Lean; they are not trusted snapshots.

```text
forall n >= 0:
    history(9+2n) = frozenForward
    history(10+2n) = frozenBackward

forward.rows.length = 73
backward.rows.length = 83
forward.saved = backward.saved; length = 12
forward.observationActive = true
backward.sourceAllowed = true
forward.report = true
```

The concrete repeated family is `[ret.M/flip(m) | p.*/m]` after every later
forward run, and `[p.M/m | ret.*/flip(m)]` after every later backward run,
for both m=T and m=U. No later forward stop test succeeds. The cold prefix
does not skip an earlier natural stop.

Every cold run is checked quiescent. Steady transitions and fixed points
are proved for **all budgets n+8**, then connected to the unbounded
`1,1,2,3,...` schedule. Accumulated Targets include all intermediate
deliveries; late NORMAL DATA does not undo an earlier control effect.
The finite diagnostic's latest completed iteration is **run-31**. No hard
limit is part of the nontermination proof.

## Modules

| Module | Checked scope |
|---|---|
| DeeperExcluded | Same complete marked-return/control machine as CarryExcluded, with changed program paths and source cut before the deeper write |
| DeeperPhase | Exact direction/budget phase equivalence, including CarryPolicy's restricted-run gate |
| DeeperFrozen | Full forward/backward witness states, not unproved transition axioms |
| DeeperRounds | Pure delivery/publication equalities for arbitrary n+8, eight sweep transitions, no future-run oracle |
| DeeperCold | Cold run-1..run-10 transitions, reached states and within-run quiescence |
| DeeperKernel | Real exclusion creation; coarse query survives carried-E policy; fine guard rejects; coarse result reaches the caller; child coverage fails; reverse demand and Targets remain |
| DeeperSteady | Arbitrary-budget transitions, accumulated forward Target, link to every later scheduled run |
| DeeperRecurrence | Exact infinite two-state recurrence, repeated row membership, no later stop, fixed points and sizes |

Current C2/C5, qualified child preparation, native definite MUST reads and
actual NORMAL DATA coverage are imported unchanged from the prior proof
family. Reference rows with concrete fields are scalar paths; ports and
call stages are fixed at their one ordinary continuation. This is not a
whole-engine or Java-front-end equivalence theorem. The native full control
still has its separate report-count/model-alignment difference.

## Reproduce

From the repository root, with compiled output outside the repository:

```bash
python3 spec/lean/proposals/deeper-excluded-guard-cycle-20261116/check.py \
  --out /tmp/deeper-excluded-guard-proofs
```

The default builds all dependencies. To reuse a checked current-policy
build, pass `--dependencies`; every parent source hash is verified first:

```bash
python3 spec/lean/proposals/deeper-excluded-guard-cycle-20261116/check.py \
  --dependencies /drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/concrete-query-exclusions-20261116/proofs-final \
  --out /tmp/deeper-excluded-guard-proofs
```

Current receipt:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/deeper-excluded-guard-cycle-20261116/proofs-final/receipt.json
```

The sibling script directory
`scripts/demand_experiments/deeper-excluded-guard-cycle-20261116` exports
finite states (`Explore.lean`) and internal pure stages (`Rounds.lean`). Set
`LEAN_PATH` to a checked output, run `lean` on the selected exporter, and
redirect its output outside the repository. `render.py` renders the complete
annotated trace from the Explore export. It never supplies a proof oracle.
Encoding: 0=p, 1=ret; fields 1=f, 2=g, 3=h; marks 1=T, 2=U.

Two new native program/component tests and nine prior carried-E tests pass.
The full native control completes **run-31/POLICY**, NORMAL report count 0,
with DemandTarget in every run. The proposed reference retains its NORMAL
observation from **run-5**; only the constructive proof establishes its
uncapped recurrence. Commands and the exact scope are in the report.
