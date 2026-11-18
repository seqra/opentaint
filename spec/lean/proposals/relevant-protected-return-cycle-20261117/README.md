# Protected relevant returns: uncapped recurrence

Constructive Lean 4.35.0. Synthetic data-flow reachability. Production unchanged.
[Code, root cause, limits and measurements](../../../../docs/reports/bidirectional-relevant-protected-return-nontermination-20261117.md).
[Complete per-block cold trace](../../../../docs/reports/bidirectional-relevant-protected-return-trace-20261117.md).

The analyzed program has two methods, three sequential calls, ordinary
allocation/return/h reads and two positive same-mark assignments to fresh
result positions. It uses one full mark T. No loop, recursion, cleaner,
configured pass, unresolved-library model or predefined summary is used.

The latest layer-aware completion functions remain unchanged. Full
NORMAL-layer closure becomes ready, but all current generated returns
have H=1. Protected replies fail every plain current-reply selection
path; relevant protected returns remain a terminal-service veto.

The package proves:

```text
forall n >= 0:
    history(2n+9)  = complete run-9 state
    history(2n+10) = complete run-10 state

forward DATA demand rows = 41
backward DATA demand rows = 47
retained NORMAL records = 6
forward DemandTarget = true
backward entry permission = true
NORMAL observation = retained from run-5
```

Every cold transition and within-run fixed point is checked. Symbolic
field-limit stage proofs and run-number regularity establish recurrence
without a hard iteration cap. No earlier forward run satisfies the stopping
predicate. Global/Dc+1/Dp+1 bounds remain mandatory; the real-E head-retention
exception never activates. Protection and layers remain separate.

| Module | Checked part |
|---|---|
| `RelevantReturn` | Existing coordinator and complete selected policy, with only the analyzed rule set/observation changed |
| `RelevantPhase` | Run-number normalization after special run-1/run-2 policies |
| `RelevantFrozen` | Explicit complete cold state witnesses |
| `RelevantCold` | Cold transitions, reached states and within-run quiescence through run-10 |
| `RelevantRounds` | Every delivery/publication stage at arbitrary additional field limit |
| `RelevantSteady` | Whole-step saturation and later-run normalization |
| `RelevantKernel` | Native-shaped same-mark protection, ready NORMAL-layer closure, relevant protected veto, retained coarse reply and ordinary h read |
| `RelevantRecurrence` | Inductive uncapped full-state recurrence, recurring demand rows, active control and no stop |
| `RelevantBounds` | Existing output/entry caps, fixed points, one mark, retained H and NORMAL basis |

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/relevant-protected-return-cycle-20261117/check.py \
  --out /tmp/relevant-protected-proofs

ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
LEAN_PATH=/tmp/relevant-protected-proofs \
lean scripts/demand_experiments/relevant-protected-return-cycle-20261117/Explore.lean \
  > /tmp/relevant-protected-cold.txt

python3 scripts/demand_experiments/relevant-protected-return-cycle-20261117/render.py \
  --data /tmp/relevant-protected-cold.txt \
  --out /tmp/relevant-protected-trace.md

./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.RelevantProtectedReturnCycleTest \
  --tests org.opentaint.dataflow.bidi.LayerAwarePointServiceNativeTest --offline
```

Optional `--dependencies` reuses completed
`layer-aware-point-service-20261116/check.py` output after source-hash checks.
The new checker source-compares every analyzer definition with `LayerBody`.
Only the analyzed rules, their reverse transfer, the one-mark rule set and
observation mark differ. It audits **176 new constructive claims; 6,455
cumulative claims in 333 source-hash-checked modules**. Only `propext` and
`Quot.sound` are allowed; there is no custom axiom, classical choice,
proof hole or native decision oracle.

All **11 native fixture/component tests pass**. The unchanged full-program
diagnostic reaches **run-31/POLICY** with zero NORMAL reports. The scoped
proposal reference retains a NORMAL observation from run-5. This inherited
model/native difference and the lack of full production NE/completion
integration remain explicit. The finite native cutoff is not a proof of
nontermination. The constructive proof concerns the selected executable
proposal; it does not refute the conditional observation-preservation theorem
or establish whole-engine/JVM/alias equivalence. No repair is selected.
Compiled proofs, raw captures and test XML stay outside the repository.
