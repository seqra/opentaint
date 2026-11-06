The exact Conductor snapshot confirms a missing frozen demand coordinate. For
the same complete run-3 call input, Current has a root ANY/FLOW guide. The
proper-prefix-off control B also has a workflowDefinition ANY/FLOW guide paired
with the same exit. B returns the additional MUST/FLOW initializer through the
unchanged C2 rule. The selected direction remains **Keep STAR; repair demand
guidance**. No emitter or admission-layer change is included.

| Terminal diagnostic evidence | Current | Control B |
| --- | ---: | ---: |
| Reached / completed / accepted run | 4 / 3 / 3 | 4 / 3 / 3 |
| Complete selected events | 1 | 1 |
| Explicit local demand rows | 77 | 175 |
| Paired rows / entry-only rows | 77 / 0 | 175 / 0 |
| Rows absent from the other recorded list | 0 | 98 |
| Returned initials | 2 | 3 |
| Invalid events / drops / caps / errors | 0 | 0 |

Both commands end at native run-4 START after complete and accepted forward run
3. Each event contains the entire bounded explicit local DATA/ZERO row list.
Static completion and shared carry are absent. The API omits Target-entry rows,
which cannot match this selected nonzero DATA query. These qualifiers permit a
comparison of the captured local lists, not a global callee-history claim.

The [evidence JSON](data/bidirectional-conductor-must-demand-snapshot-20261106.json)
embeds both exact raw event records, so every row entry, paired exit, original P,
actual DAG, returned initial and complete typed catalog can be recovered. It also
embeds both manifests and runtime checks, decoder/test/packaging source, unchanged
C2 source, selected normalized pairs, and hashes for full logs and controls.
Twelve decoder tests, 13 selected-witness checks and 16 packaging checks pass.

Both terminal manifests record repository HEAD `94dc8549f` and production
revision `8331bf9e`. The evidence JSON uses these manifest revisions. Its embedded
original packager used the earlier report HEAD `f40e83b52`; this label is corrected
in the package. No executable production source changed between those HEADs.

The matched call is `WorkflowExecutorOps#startWorkflow(StartWorkflowInput)` to
`WorkflowExecutorOps#createAndEvaluate(WorkflowModel)`, physical call 9, stage 3,
ROOT scope `(0,-1)`. Both callee keys have entry index 18 and the same native
Empty-context bytes. The complete caller/P/call key matches, as does pure query
`2d4642a06869395d21b1a14a86f54d47f4eeede366566207f111787138675a6e`.
Configuration, analyzed source/IR and native context prerequisites also match.
Catalog integers and identity hashes are not cross-process identities.

The actual in both events is NORMAL
`arg0.<WorkflowModel.workflowDefinition:WorkflowDef>.MUST/Graal`, with empty E and
null protection. Its native DAG has an empty root, one field edge and a terminal
uniform Graal membership; it has no exact membership. MUST is thus verified at
the actual head, not inferred only from a packet header.

The following abbreviations denote complete typed fields:

- `wfDef`: `com.netflix.conductor.model.WorkflowModel.workflowDefinition`, type `com.netflix.conductor.common.metadata.workflow.WorkflowDef`.
- `taskListener`: `com.netflix.conductor.core.execution.WorkflowExecutorOps.taskStatusListener`, type `com.netflix.conductor.core.listener.TaskStatusListener`.
- `workflowListener`: `com.netflix.conductor.core.execution.WorkflowExecutorOps.workflowStatusListener`, type `com.netflix.conductor.core.listener.WorkflowStatusListener`.

All listed entries and exits are FLOW with empty E and mark exclusions. Row
ordinals are zero-based serialization positions, not engine IDs.

| Variant / row | Entry | Its paired exit |
| --- | --- | --- |
| Current 15 | `arg0.ANY/FLOW` | `this.taskListener.ANY/FLOW` |
| B 0 | `arg0.ANY/FLOW` | `this.taskListener.ANY/FLOW` |
| **B 16** | **`arg0.wfDef.ANY/FLOW`** | **The same `this.taskListener.ANY/FLOW`** |
| Current 30 | `arg0.ANY/FLOW` | `this.workflowListener.ANY/FLOW` |
| B 55 | `arg0.ANY/FLOW` | `this.workflowListener.ANY/FLOW` |

Current's complete local list contains no `arg0.wfDef.ANY/FLOW` entry. B has one,
with the taskListener exit. The workflowListener exit must not be attached to
that child guide. Current's recorded row set is a strict subset of B's set.

Current returns `wfDef.STAR/FLOW` NORMAL and `wfDef.STAR/Graal` DEMAND. B retains
both and adds `wfDef.MUST/FLOW` NORMAL. The unchanged policy advances one field
from a root ANY guide and emits STAR. An ANY guide at the actual MUST head can
preserve MUST. The snapshot now observes the frozen coordinates that were
source-inferred in the [upstream admission report](bidirectional-conductor-upstream-admission-20261106.md).
The observer does not capture a per-row emission binding; that explanation still
uses the pinned source rule.

The verified B control replaces only
`samePoint(minus(key.node.leaf, key.above))` with `samePoint(key.node.leaf)` in
`canonicalSpans`. Its saved audit passes 60 checks: all class ABIs match and only
that method's executable code changes. Same-point MAY/exact and across-header
rules remain active. This controls the difference across the paired executions;
it does not observe one earlier B2 normalization mutation. It also affects
NORMAL actual packets, so it is broader than a guidance-only repair.

The [uniform native case](bidirectional-uniform-prefix-refinement-reproducer-20261106.md)
shows the matching operational effect: STAR/FLOW reads to MAY/DEMAND, while
MUST/FLOW reads to MUST/NORMAL. Current first reports at run 5 and B at run 3;
both naturally converge at run 5 with one finding. The snapshot and that small
case establish a real guidance/admission precision difference and a refinement
delay. They do not prove that this guide is required for either final missing
Conductor finding. P0 remains unresolved. No full-run quality, convergence or
performance conclusion follows from these captures, and no analyzer fix is
included.
