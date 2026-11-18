# Consolidated proposal: rule-by-rule soundness audit

17 November 2026. Constructive Lean 4.35.0. Production unchanged.

[Audit and 30-rule proof map](../../../../docs/design/bidirectional-demand-termination-soundness-audit-20261117.md).
[Proposal](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md).
[Root-cleaner / getter gap and iteration trace](../../../../docs/reports/bidirectional-cleaner-getter-soundness-gap-20261117.md).

**Repair update:** the [disjoint-cleaner proof delta](../disjoint-cleaner-flow-20261117/README.md)
closes the named gap in the proposal and retains its NORMAL observation at
run-3. Production is unchanged. The original audit/countermodel below are
historical proof inputs for that delta.

**No whole-analyzer soundness theorem is claimed.** The original audit verified a
retained admission gap: the native cold case stops at **run-3** without its
reachable observation. The selected C2/C5 model rejects the same precise
input. Two controls recover one NORMAL observation, also at run-3.

The package adds **72 claims** to the audited 7,009-claim chain: **7,081
cumulative, 407 source-hash-checked modules**. Counterexample theorems are
included in this count. All named declarations have their transitive axiom
closures checked; only `propext` and `Quot.sound` are permitted. No custom
axiom, classical choice, proof hole or external decision oracle is used.

| Module | Scope |
|---|---|
| `AuditKernel` | Constructive positive-Horn simulation, complete ND conjunctions, translated service witnesses, quiescent order independence |
| `AuditGeometry` | MAY partition, genuine cuts, read/write geometry, whole uniform support for arbitrary finite positive rules |
| `AuditServices` | Complete raw C2-image witnesses; countermodels separating point coverage, query identity and needed service |
| `AuditScopedService` | Same-frame native NORMAL receipts; stale/foreign/D/saved/backward/GROUP/run-1 guards |
| `AuditNormalization` | Finite NORMAL prefix-path correlation and guarded suffix transport; limits of empty-suffix evidence |
| `AuditReplySafety` | Whole native return coverage preserves positive continuations, without an external monotonicity premise |
| `AuditIntersection` | Generic scalar paired-C5 point preservation with real E, arbitrary paths/tails, cuts and literal header preservation |
| `AuditCleanerGetter` | Retained admission counterexample: selected C2/C5, root cleaner/read, bindings, precise rejection, concrete witness |

These are scoped model theorems. The audit states four remaining bridges
to whole-analyzer execution. The cleaner/getter case refutes a required
cross-iteration sufficiency claim; it is not repaired by adding proof
assumptions. Its reference/native structural-companion difference is
explicit: even retaining the native NORMAL companion cannot supply T.

Validation also runs **53 native tests**: 50 component checks and three
cleaner/getter diagnostics. The loss test asserts current broken behavior;
it is not a passing correctness regression. Native tests do not install NE
or the proposed delivery selector. The inherited termination family remains
252 configurations, natural stops by run-9, diagnostic scan through run-25.
Its historical unchanged native diagnostic remains run-31/POLICY. None is a
universal termination/no-missed-observation theorem.

```bash
python3 spec/lean/proposals/termination-soundness-audit-20261117/check.py \
  --out /tmp/termination-soundness-audit

./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.BoundNativeReplyServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.DefiniteMustReplayNativeTest \
  --tests org.opentaint.dataflow.bidi.DefiniteReplySupportNativeTest \
  --tests org.opentaint.dataflow.bidi.NormalUniformActualCoverageTest \
  --tests org.opentaint.dataflow.bidi.PointWriteProgressNativeTest \
  --tests org.opentaint.dataflow.bidi.ExclusionChildReplayNativeTest \
  --tests org.opentaint.dataflow.bidi.ConcreteQueryExclusionsTest \
  --tests org.opentaint.dataflow.bidi.CleanerGetterAdmissionSoundnessTest --offline
```

`check.py --dependencies PATH` reuses a parent receipt only after checking
all current dependency source hashes. Logs, compiled objects, XML and
receipts are external to the repository:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/termination-soundness-audit-20261117/
```
