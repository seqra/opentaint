# Retain required demand guidance; keep scalar C2 unchanged

Status: **behavioral direction selected; FLOW/DEMAND/ANY producer correction
implemented; full validation in progress**. The user selected **Keep STAR;
repair demand guidance**. The correction implements the bounded producer path
specified below. It is not a whole-engine correctness or quality claim.

Keep `RestrictedInitialPolicy.emit`, `canEmitInitial`, `canStoreInitial`,
admission layers, field transfer, native MUST application and NormalTarget
support unchanged. Keep NORMAL data-only MAY canonicalization and existing
CertifiedNormalFlow, NonSubsumable, alias, static and ownership laws. The change
is retention of required guide coordinates before they
are lost, with exact original and paired exit/port labels.

## Observed guide-to-image difference

The [complete local Conductor snapshot](../reports/bidirectional-conductor-must-demand-snapshot-20261106.md)
has identical complete Current/B run-3 call inputs: Ops
`startWorkflow(StartWorkflowInput)` calls `createAndEvaluate(WorkflowModel)`,
physical call 9, stage 3, ROOT `(0,-1)`, Empty context, field limit 2.
Both actuals are NORMAL `arg0.workflowDefinition.MUST/Graal`, empty E and no
protection. Current has 77 paired local rows; B has 175, including all 77.

| Captured row | Entry | Its paired exit |
| --- | --- | --- |
| Current 15 / B 0 | `arg0.ANY/FLOW` | `this.taskStatusListener.ANY/FLOW` |
| B 16 | `arg0.workflowDefinition.ANY/FLOW` | **The same taskStatusListener exit** |
| Current 30 / B 55 | `arg0.ANY/FLOW` | `this.workflowStatusListener.ANY/FLOW` |

`workflowDefinition` belongs to `com.netflix.conductor.model.WorkflowModel`,
type `com.netflix.conductor.common.metadata.workflow.WorkflowDef`.
`taskStatusListener` belongs to `com.netflix.conductor.core.execution.WorkflowExecutorOps`,
type `com.netflix.conductor.core.listener.TaskStatusListener`; the other listener
has type `com.netflix.conductor.core.listener.WorkflowStatusListener`.
All listed entries/exits have empty E and FLOW mark exclusions. Do not attach
the workflowStatusListener exit to the child guide.

Unchanged scalar C2 explains the operational distinction:

```text
d0 = arg0.ANY/FLOW                 a = arg0.workflowDefinition.MUST/Graal NORMAL
d1 = arg0.workflowDefinition.ANY/FLOW
emit(d0, a) = workflowDefinition.STAR/FLOW NORMAL
emit(d1, a) = workflowDefinition.MUST/FLOW NORMAL
```

Current returns STAR/FLOW NORMAL and STAR/Graal DEMAND. B retains both and adds
MUST/FLOW NORMAL. The row difference is observed; native per-row emission
binding is not. Both captures end at reached/completed/accepted 4/3/3. They do
not prove that this initial is necessary for either final Conductor miss.

The effect also applies to exact inputs. For an existing root ANY/FLOW guide,
an exact `p.f.$/T` input emits `p.f.*/FLOW`. A retained same-head `p.f.[any]/FLOW`
guide emits the existing `p.f.$/FLOW` initial as well. This is an extra worker
through the current emitter, not a new exact-emission rule. Summary storage
uses the existing EXACT-to-STAR normalization and keeps its mark exclusions.
The named-field cleaner test checks the extra backward initial while keeping
its cleaner, native-record, source-permission and final finding assertions.

## Earliest native producer boundary: observed versus inferred

The [uniform native reproducer](../reports/bidirectional-uniform-prefix-refinement-reproducer-20261106.md)
shows the same mechanism with two methods. Its B2 Current/B processed rows are
identical. In repository trace lines 175/176, `arg0.f.ANY/FLOW DEMAND` is
processed at mapper points 1/0; later lines 181/182 process `arg0.ANY/FLOW
DEMAND` at those points. Both have original `ret.Element.ANY/FLOW`. The final
summary at line 165 is root-only in Current and root-plus-child in B.

The first **source-inferred** pruning is point 1, the neutral branch join:

```text
runStatement -> emitUnchanged -> completeOutput -> admitOutput
 -> ScopedEdgeStore.addAll -> ConclusionGroup -> FlowGroup.addAll
 -> addInto merges the later root with the retained child
 -> canonicalFlowState -> canonicalRegions -> canonicalSpans
 -> minus(node.leaf, above) removes the child
```

Point 0's boundary store and final summary store repeat the same opportunity.
`onProcess` runs before those post-statement admissions, so identical processed
rows do not imply identical retained stores. No close transaction was captured
in this small trace; the point-1 attribution follows its order and pinned code.
Final summary loss is directly observed. Current first reports at run 5 and B
at run 3; both naturally converge at run 5 with one finding.

For the exact Conductor row, `HandOff.toForward` projects admitted backward
summary leaves to `(guidancePattern(piece), guidancePattern(original))`.
Therefore B's frozen row requires the corresponding backward summary coordinate
under the taskStatusListener original. The wrapper source calls
`createAndEvaluateWithLock`, then `decide`; those are producer-route checkpoints,
not a captured derivation of this row. The precise point/summary admission that
first removed this **workflowDefinition** coordinate is unobserved. Earlier
Conductor point/summary removals for taskDefinition are separate evidence and
must not be relabeled as this transaction. FLOW mx is erased at guidance
projection; the frozen empty mx does not establish the producer's mx.

## Why a late demand trie alone is insufficient

`DemandStore` already has a separate entry trie and complete paired rows.
`Builder.index` inserts each retained entry without synthesizing descendants.
If the final summary is root-only, neither handoff nor another entry trie can
recover the missing child. Reading `summaries.demandEdges` later is too late.

Capturing admitted summary offers before summary canonicalization could retain
the child in the uniform fixture's recorded child-first order. It is a narrower
diagnostic candidate, but not a both-order repair. At `endAt`, `admitOutput`
gates `retainSummary`. If the parent reaches point 1 first, existing
`FlowGroup.subtractSubsumed` drops a later child and returns no delta. That
child never reaches the method boundary or the late collector. A collector
before semantic restriction/C5 would instead risk exporting unadmitted rows.

This is a concrete source-level parent-first counterexample using the same
root/child facts; that alternate schedule has not been run. It establishes the
need to address producer admission/freshness, not a need to edit all 39 consumers.

## Narrow candidate for the known FLOW/DEMAND failure

The known lost guide facts are already effective **FLOW, DEMAND, ANY** in B2.
No NORMAL-to-GUIDE transition is needed to explain them. Every DEMAND result
satisfies the unchanged `selectedForHandoff`. Thus the demonstrated subdomain
can be recognized without a premise-dependent role:

```kotlin
// Review sketch; not implemented. No owner or manager metadata is added.
fun preserveKnownGuideHeads(f: Facts): Boolean =
    f is FlowTree && f.layer == Layer.DEMAND && f.tail == Tail.ANY
```

| Required store/view path | Candidate change in that subdomain |
| --- | --- |
| Cold `canonicalFlowPacket` | Retain explicit parent and child heads. |
| `FlowGroup.addInto/subtractSubsumed` | Do not treat an ancestor as an equal-coordinate duplicate; return a fresh child delta. |
| Warm `canonicalFlowState/canonicalRegions` | Keep those heads after same-header merge and across-header prefix subtraction. |
| Point, summary and publication groups | Reuse that admission law; preserve current state and deltas, not historical inputs. |
| `canonicalPackets` on this FLOW packet | Do not erase heads again before delivery/query/handoff. |
| Handoff and existing DemandStore | Enumerate retained leaves with their original and exact paired exits; no synthetic row. |

Conceptually the fresh guide part is a coordinate difference, not region cover:

```text
old {p.ANY/FLOW}, offer {p.f.ANY/FLOW}
Current prefix test: no fresh denotation -> no child delta
candidate: raw equal-coordinate trie union/difference -> fresh child
```

Use existing current tries and raw merge/delta operations. Retain existing
same-point/header laws only where their projected FLOW guide-coordinate image
is preserved. Do not automatically roll back E/mx joins or concrete MAY/exact
rules. This is a candidate for the known subdomain, not a claim that DEMAND-only
normalization is a complete repair for all guide kinds. A change only to the
one `canonicalSpans` expression is insufficient for both arrival orders.

The 39-call-site audit is a **checklist**, not a requirement for 39 signature
changes or a selected three-mode architecture. For this intrinsic subdomain,
existing dispatch can carry the revised pure view without per-owner PacketUse
metadata. Normal TaintTree actuals, scalar C2, image, layers and current cache
keys need not change merely to retain these FLOW guide coordinates.

## Producer implementation cell

Use the following changes for the demonstrated FLOW/DEMAND/ANY path. This is a
correction to guidance compaction. The data view and the scalar emitter keep
their current rules. A retained demand head can add refinement work.

```kotlin
// SpatialCanonical.kt: real FLOW packets only.
internal fun FlowTree.keepsDemandPositions(): Boolean =
    layer == Layer.DEMAND && tail == Tail.ANY

internal fun ApManager.canonicalFlowPacket(value: FlowTree): FlowTree =
    if (value.keepsDemandPositions()) value else canonicalFlowDataPacket(value)

// Move the existing function body here without a semantic change.
internal fun ApManager.canonicalFlowDataPacket(value: FlowTree): FlowTree {
    /* existing same-tail DATA normalization */
}

// canonicalRegions gains an optional preserveAnyHeads = false argument.
// canonicalFlowState sets it to first.layer == Layer.DEMAND.
// Taint state calls leave it false.
val keepHeads = preserveAnyHeads && value.tail == Tail.ANY
var root = if (!keepHeads && value.tail in setOf(Tail.ANY, Tail.ANY_TAINT))
    canonicalSpans(value.root, value.exclusion, m, { it }) else value.root
val belowAllowed = !keepHeads && stored.tail in setOf(Tail.ANY, Tail.ANY_TAINT)

// Groups.kt, FlowGroup.subtractSubsumed:
val belowOk = !t.keepsDemandPositions() && marks &&
    (stored.tail == Tail.ANY ||
     stored.tail == Tail.ANY_TAINT && t.tail == Tail.ANY_TAINT)
// Keep the current same-coordinate atOk predicate and header joins.

// DiagonalRelations.kt: this FLOW tree is TAINT geometry, not FLOW guidance.
val packet = m.flowTree(/* existing packed-TAINT geometry and headers */)
offered.copy(geometry = m.canonicalFlowDataPacket(packet).root)
```

The diagonal adapter change is required. Its temporary FLOW tree can have
DEMAND/ANY headers. Letting that surrogate use the real-FLOW exception would
also change concrete TAINT normalization. Keep the adapter on the old DATA
function. The source audit found one such direct call. Other existing
`canonicalPackets` calls keep their signatures and use the real packet kind.

Do not change equal-point E/mx union, MUST fill, cross-tail admission, budgets,
protection, owner keys, fact equality, or cache keys. At a common coordinate,
the existing mx intersection still represents the union of admitted marks.
The producer model checks this request-union law for its finite FULL table.
Equal handoff projections alone are insufficient to prove runtime request
equivalence, so the runtime mx controls remain required.

Required native evidence before a production correction is accepted:

1. Cold packet, parent-first and child-first FLOW/DEMAND/ANY admissions retain
   both positions. The child is fresh after its parent; an exact repeat is not.
2. The point, summary and publication owners keep those positions and their
   original/exit pair. Handoff uses the existing demand builder.
3. FLOW NORMAL and MUST controls keep their old compaction. Concrete TAINT,
   including the packed diagonal surrogate, keeps its old compaction too.
4. The uniform and exact-prefix programs pass their run-3 checkpoints with
   STAR emission unchanged. Their natural traces must also finish.
5. Default native tests and the configured project campaign pass their stated
   gates. No old B overlay is applied to the changed normalizer class.

The initial native producer check has eight expected failures and four passing
controls before correction. After correction, all 29 targeted producer/spatial
checks pass. Both exact-prefix and uniform-source programs report in run-3;
their natural traces complete run-5. The separate shared-loop program still
completes run-5 with zero reports and fails its finding assertion. Keep that
failure as an open coverage issue. These small results do not replace the
configured project campaign.

## General contract and proof boundary

The existing selector also includes NORMAL backward ZERO and NORMAL ND results.
Those are outside the demonstrated FLOW/DEMAND producer failure. If retaining
all selected operational members needs owner context there, derive it from full
original/current direction for actuals and stored original/source direction for
records. Do not substitute a matched callee member or reintroduce GroundingSupport.
No native NORMAL-to-GUIDE counterexample has been established for this regression;
the broader role transport is an unproved candidate, not a prerequisite assumed
from the model or a reason to change NORMAL data-only MAY normalization now.

The [finite model](../../spec/lean/proposals/demand-guidance-retention-20261106/README.md)
passes 39 local lemmas with the unchanged scalar C2 model. Its
`pairedAdmissionImage` retains opaque complete exit labels; it is **not
production C5**. Scope: finite FULL scalar lists, ordinary nonstatic bases,
counted fields, empty E. ZERO/ND occur only in the selector table. It proves
exact row union/images in both orders and that a late store cannot recover an
already discarded child. The producer extension proves coordinate add/delta,
exact duplicate suppression, handoff pairing, and the current same-head mx
request-union law in a finite FULL table. It does not prove native producers,
role transitions, C5/budgets or whole-engine effects. The models use only
`propext` and `Quot.sound`; see the `checks.json` axiom audit.

Next proof/test work is bounded to the candidate producer path: cold packet,
both arrivals, warm point/summary/publication admission and fresh deltas;
post-C5 paired handoff; unchanged scalar C2 and NORMAL data controls; uniform
F3 checkpoint and natural trace. The concrete same-point MAY/EXACT guide model
is a separate scope check before generalizing beyond FLOW ANY. Keep existing
CertifiedNormalFlow, protection and normal-target tests. Do not claim final
Conductor recovery, full quality, convergence or performance until validated.
