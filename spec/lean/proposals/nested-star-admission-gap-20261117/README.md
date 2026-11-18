# Nested same-head STAR admission counterexample

17 November 2026. Constructive Lean 4.35.0. FULL mode.
[Complete code and per-run trace](../../../../docs/reports/bidirectional-nested-star-soundness-gap-20261117.md).
[Consolidated contract](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md).

**New open soundness gap:** a wrapper offers STAR/FLOW to a precise STAR/FLOW
entry in run-2. The selected C2 emits nothing. The inner one-field overwrite
cannot publish the NORMAL summary that preserves its sibling g. The
controlled cold native run stops at **run-3**, with zero findings. Current
production retains one NORMAL finding at run-3. No production change is made.

`NestedSTAR` adds **16 constructive claims**: **7,124 cumulative in 410
source-hash-checked modules**. It imports C2/C5 from the selected proposal,
models the ordinary field-write subset used by this code, and includes
argument outputs, the direct C5 record, its genuine f guard, concrete g
survival and an empty-handoff quiet suffix. There is no real field cut,
cleaner, loop, recursion, configured pass, static or ND in this example.

Three native tests cover four cold scenarios: current policy succeeds at
run-3; the one-cell protocol adapter loses the finding at run-3; a direct
call succeeds at run-3; a no-write nested call succeeds at run-1. The adapter
checks both the denied native start and actual STAR offer. It changes only
test delivery, not production admission. The focused model/controller is
not a formal model of the entire JVM or complete proposal implementation.

The separate 784-configuration follow-up sweep reached fixed points at
each run and observed no mismatch against its concrete reference; natural
stops were run-3 through run-13, with diagnostic captures through run-25.
Its helpers are conditional marking programs, not this ordinary overwrite
helper. That search did not cover this mechanism. Some initial E/H cases
are packet controls, not direct source-rule outputs. See the [follow-up report](../../../../docs/reports/bidirectional-demand-soundness-followup-20261117.md)
for the exact scope and counts.

```bash
python3 spec/lean/proposals/nested-star-admission-gap-20261117/check.py \
  --out /tmp/nested-star-proofs
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.NestedOverwriteStarAdmissionTest --offline
```

The checker verifies every dependency source hash, compiles the new model
and audits every named theorem's transitive axioms. Only `propext` and
`Quot.sound` are permitted. No classical choice, custom axiom, proof hole
or external decision oracle is accepted. `--dependencies PATH` reuses the
previous checked proof receipt. No hard limit proves the loss.

All logs, XML, compiled modules and receipts are outside Git:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/soundness-followup-20261117/
```
