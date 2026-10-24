# Thingsboard run-1: FLOW and concrete-mark overlap

Date: 24 October 2026. Runtime: `40e20d16f03ab046df75a53a489bb331b065a9c1`.
Latest reached: **run-1 OOM**. Latest COMPLETE: **none**. Latest accepted
forward report: **none**. No project command was rerun for this investigation.
Analyzer implementation is unchanged.

This report reopens the corrected Thingsboard snapshot from the
[performance report](bidirectional-rule-selection-performance-20261024.md).
Heap SHA-256: `20d118e9290b77d232f50684600f047aa90a77ee9222531da73e81617aa6932d`.
The design baseline is the original demand-driven emission and restriction
in [ap.md](../../spec/ap.md), **without StrongQueries**. Current runtime
measurements remain useful: StrongQueries does not run in run-1.

## 1. The tail mismatch is real, but it is not the only common pattern

The complete physical header census gives:

| Kind | Layer | Tail | Physical headers |
| --- | --- | --- | ---: |
| FLOW | NORMAL | `*` | 510,501 |
| FLOW | DEMAND | `*` | 48,689 |
| FLOW | DEMAND | `[any]` | 577,801 |
| TAINT, with any leaves | DEMAND | `[any]` | 12,219,715 |
| TAINT, with any leaves | DEMAND | `[any-taint]` | 10,848 |
| TAINT, exact leaves only | DEMAND | `$` leaves | 17,124 |

The partitions total 1,136,991 FLOW headers and 12,247,687 TAINT headers,
exactly matching the independent complete class histogram. The complementary
NORMAL TAINT and NORMAL FLOW/ANY categories are zero. A header can occur
under several owners. These are physical objects, not processed-edge counts.

99.77% of physical TAINT headers have DEMAND/ANY leaves. FLOW/ANY is also
common. Thus the useful candidate is broader than sharing a FLOW/STAR
template with TAINT/ANY: many marked relations already have an uncorrelated
FLOW/ANY counterpart.

The source explains the patterns:

```text
I(p, STAR, *) starts as p/STAR/* NORMAL.
I(p, STAR, T) starts as p/ANY/T DEMAND.

Layer demotion alone keeps a FLOW STAR tail.
A read below a broad FLOW leaf can produce FLOW ANY.
A field-limit cut or a may-target transfer can also produce ANY.
```

`initialFacts`, `EdgeApplication.flow`, `run1CoverFacts` and `withLayer`
implement these separate decisions. Do not change STAR to ANY merely to
make two headers match. That loses input/output suffix correlation.

## 2. Exact comparison at the same method and statement

The existing stress sample has eight method stores, chosen for high premise
counts and at most 64 statement slots. It includes `DefaultTbContext.enqueue`,
`enqueueForTellNext`, `DefaultTransportService.sendToCore`, MQTT handlers and
`saveTimeSeriesInternal`. It is deliberately biased and is not a project-wide
sample.

The new decoder joins the original array/initial ownership with every FLOW
map, header and trie leaf in those same stores. It compares the same complete
input geometry, with only the input mark removed, at the same statement.
It retains base, paths, layer, tails, E, mark exclusions and original origins.
The heap's canonical atom table has 410 FULL atoms and control ZERO; there
are no GROUP atoms in these FULL exclusions.

The first coverage test is deliberately narrow:

```text
FLOW:  I(p, STAR, *) -> q/ANY/(* minus X), DEMAND
TAINT: I(p, STAR, T) -> q/ANY/T,           DEMAND
T not in X; same complete input geometry and same output base/path.
```

| Same eight method stores | Count |
| --- | ---: |
| Occupied concrete cells | 9,584 |
| Concrete output leaf/mark memberships | 29,151 |
| Same-input-mark memberships | 29,115 |
| Covered by same-path FLOW/ANY | 18,869 |
| Only a same-path FLOW/STAR counterpart | 7,719 |
| FLOW exists, but no same output leaf | 2,527 |
| Different output mark | 36 |
| Fully covered concrete cells | 2,240 |
| Partly covered concrete cells | 3,381 |

The narrow relation test covers 64.73% of retained marked memberships in
this sample. It does not establish that the same fraction of historical
operations, bytes or the whole-project workload can be removed. It also
does not establish preservation across a later run.

## 3. The method summaries have more overlap

The exact eight owners have 1,217 raw summary premise rows: 1,157 concrete,
52 FLOW and eight ZERO. All concrete output memberships here are DEMAND/ANY.

| Exact eight-method summary scope | Count |
| --- | ---: |
| Concrete output leaf/mark memberships | 11,752 |
| Covered by same-path FLOW/ANY | 10,631 |
| Only a same-path FLOW/STAR counterpart | 1,049 |
| No same output leaf | 72 |
| Fully covered concrete premise rows | 36 |
| Partly covered concrete premise rows | 887 |
| Rows with no covered output | 234 |

90.46% of marked output memberships pass the narrow local relation test.
But only 36 of 1,157 whole premise rows disappear. Partial subtraction is
essential. A whole-tree-only optimization misses most of the opportunity.
Conversely, removing most leaves does not imply removing most premise arrays
or caller candidate keys.

The 10,631 covered memberships form 399 FLOW-output families: 367 of width
28, six of width 18, thirteen of width 10 and thirteen of width nine.
These are exact same-input/same-output FULL memberships, not a Cartesian
product of input and output mark sets.

### Static conclusions dominate the covered outputs

| Summary output base | All marked memberships | FLOW/ANY-covered |
| --- | ---: | ---: |
| Static | 10,523 | 10,523 |
| Argument | 1,005 | 108 |
| This | 224 | 0 |

Most covered outputs have non-static origins: argument-origin summaries contribute 7,611
covered outputs and `this` origins contribute 2,912. Static origins contribute
108. Static conclusions can be emitted and promoted as summaries without
being propagated as intraprocedural static-base facts.

Resolving canonical accessor IDs exposes a repeated target pattern:

| Covered static class | Marked memberships |
| --- | ---: |
| Synthetic `__spring_registry__` | 7,311 |
| `TbCallback` | 803 |
| `TbMsgCallback` | 803 |
| `TenantId` | 803 |
| `TbMathNode` | 803 |

There are 13 target fields. Twelve have 803 covered memberships each;
`__spring_registry__.TbClusterService` has 887. The other targets include
`TbCallback.EMPTY`, `TbMsgCallback.EMPTY`, `TenantId.tenants`, `TbMathNode.locks`
and eight other Spring registry service fields. This is a repeated static
target/initial-mark relation, not 10,523 distinct static fields. It is not
the old EntityType enum matrix. The census does not by itself identify the
exact alias/call derivation responsible for each target, or prove that the
target may be discarded.

One exact example is `DefaultTransportService.sendToCore`:

```text
Input: TenantId.tenants, mark #61.
Outputs: argument 4 at fields [28100], [32912], [49324], ANY/#61, DEMAND.

The FLOW summary has those same three outputs, ANY/(* minus {#1,#3}), DEMAND.
#61 is admitted. All three marked outputs pass the local coverage test.
```

Field 32912 is `DefaultTransportService.ApiStatsProxyCallback.callback`.
The other two are the captured `this$0` fields of two
`DefaultLwM2MOtaUpdateService` callbacks. The numerical IDs remain in the
artifact so this example can be checked against the exact heap.

Another example has argument 1 as its initial and only its identity-like
output. TAINT is `arg1/ANY/#104 DEMAND`; FLOW is `arg1/STAR/* NORMAL`.
That pair fails ANY relation subsumption because STAR preserves suffixes.
It remains a candidate for exact geometry sharing with a mark mask.

## 4. Where the unnecessary work can occur

Today, a marked premise and an abstract premise have separate storage rows.
`ConclusionGroup` checks subsumption within a kind/premise; it does not compare
these cross-premise FLOW and TAINT relations. Equal tail kinds alone do not
fix this separation.

Both relations can therefore be retained, published, matched at callers,
applied and handed off. The caller path indexes geometry before the complete
mark test. For k marked inputs and k marked summaries, that candidate stage
can examine a k-by-k family before the AP predicate rejects mismatched marks.
The source establishes that possible work pattern, not its measured share.
Pruning only some conclusions can leave all k premise keys present.

FLOW-first worklist processing can make the covering summary available
before a marked result reaches publication. Current changed work is LIFO;
FLOW and TAINT share `other`, while unchanged work has its own priority.
A useful policy must cover both FLOW changed work and FLOW unchanged work,
within the existing ZERO/control phase, rather than letting a TAINT unchanged
burst always run before queued FLOW. Keep the repeat-set, quantum and
request/static barrier contracts. No global FLOW-completion barrier is needed.

## 5. Design split

1. **Remove proved redundant summary effects before publication.** Subtract
   covered leaves across corresponding input keys. Keep the FLOW relation
   and every uncovered marked residual. If the retained FLOW demand is proved
   to replace the marked demand under the original AP pipeline, omit that
   marked demand too. Do not retain a per-mark demand merely because the
   covering FLOW is DEMAND. Late coverage compacts existing rows without
   replaying prior observations.
2. **Share residual geometry.** STAR-versus-ANY is not semantic subsumption.
   A FLOW reference plus exact mark sets and original TAINT annotations can
   replace repeated geometry while preserving these marked demands.
3. **Give FLOW method work priority.** This increases the chance that step 1
   removes work before publication. Correctness must hold for either arrival
   order. It does not require waiting for other methods to finish FLOW.

Start at summary admission, after required producer/observation effects and
before publication. Do not drop intraprocedural T arrivals which must evaluate
CM predicates. A static TAINT supply cannot be replaced by a markless FLOW
write: actual group availability must still be established. Preserve computed
static supplies before removing redundant summary storage/transport.

## 6. Original AP handoff, with no StrongQueries

The original abstract demand emits a shared FLOW initial. It does not start
a concrete analysis merely because a marked input arrives. A concrete caller
input can then instantiate the callee's FLOW summary through ordinary summary
application. The replacement proof must use that path.

The current general actual-input fallback was introduced in commit
`28a123f0e` on 16 October, with the old guidance-only run-1 handoff design.
It replaced per-demand emission and also added current-query response
permission. The 22 October static query completion extended that mechanism;
it did not introduce the general fallback. The optimization design does not
inherit this later-run semantic change or require its general use.

A T-to-U dependency with `T != U` cannot be covered by mark-preserving FLOW.
Conditional source emission preserves the incoming premise in
`RunMethodLocalServices`: the unary callback emits under `premise`; a run-1
multi predicate emits each contributing origin. Thus such residuals can retain
the T-to-U demand. Sink T seeds also remain. A CM check by itself does not
exclude T from FLOW; a cleaner/mark-removal action can.

However, a local abstract-pair inclusion theorem is not a complete handoff
theorem. A same-mark generating rule can be redundant in the coarse run-1
image while adding a real flow:

```java
x = p.right;
// Conditional source: CM(p.left, T) => assign T to x.
return spread(x);
// The configured spread pass has an ANY target.
```

Run-1 starts both `I(p,STAR,*)` and requested `I(p,STAR,T)`. The ordinary read
gives FLOW/ANY at x. The source can give exact T at x; spread makes its output
TAINT/ANY. The FLOW/ANY summary contains that marked run-1 pair image.

With only `p.left/T` present, the real read of `p.right` supplies no T to x;
the source does. The original abstract backward query does not execute the
reversed concrete source gate. Skipping that rule in later iterations based
only on the old coarse image therefore needs a stronger justification.

### Selected correction: non-subsumable conclusions

The chosen correction does not inspect CM definiteness. It adds an edge
annotation for concrete conclusions:

1. A rule assigns T under an original T premise: protect its T conclusion
   from FLOW subsumption.
2. Applying a summary with a protected conclusion protects the caller result.
   Ordinary transport also carries existing input protection.
3. Composing `T -> U` with `U -> T`, where `U != T`, protects the resulting
   T conclusion.
4. Identical copies merge with OR: if either is protected, keep one protected
   copy. A later protection-only change must propagate even if the T fact is
   already stored.

In the example, the source assigns T under `I(p,STAR,T)`, so its output is
protected. The coarse FLOW may cover its pair image, but cannot remove this
marked demand. A T-to-U dependency with different marks remains uncovered
in the first place. These rules preserve the needed original marked-demand
route without adding general actual-input query admission.

The flag belongs to a logical edge/leaf/mark, not to global T. CM still checks
T and cleaners still remove T under the existing rules. No field, mark-group
or rule-condition semantics change. Preserve the flag through calls,
static effects, masks and ordinary transport; retain ordinary observation
identity when only the flag grows. Strip the run-1 annotation at handoff
after keeping its normal FULL T demand. Later runs need no new mark token.

Static conclusions have the same rule. Do not erase actual pool supply
effects or use a FLOW write to manufacture a reached T. Summary subtraction
is separate from those effects.

The snapshot has no protection flag, so the measured overlap is a candidate
count before protection. It is not a measured final deletion count. The full
inter-run simulation for this corrected protocol remains to be proved.
No runtime rule skip, flag or demand erasure was implemented.

## 7. Checked proof scope and evidence

[Run1FlowTaintCoverage.lean](../../spec/lean/ApSpec/Run1FlowTaintCoverage.lean)
uses the existing original AP model, not a replacement mark model. Its local
proofs check cross-premise ANY coverage, the T-to-U obstruction, mark exclusions,
the STAR/ANY counterexample, the original abstract/concrete emissions, and
the concrete steps of the same-mark GEN example above. It also checks the
selected assignment, summary, cycle and OR-merge protection laws, including
late protection growth. The local model does
not prove the full interprocedural simulation, source/sink observation parity,
or sound removal of every covered marked demand.
Its 28 declarations pass `lake env lean ApSpec/Run1FlowTaintCoverage.lean`;
the axiom audit contains only `propext` and `Quot.sound`.

The artifact directory contains exact decoders, reports and receipts:

- [Method-point comparison](../../../run1-rule-selection-equality-fix-20261024/validation/flow-taint-patterns-20261024/pattern-analysis.json).
- [Exact summary comparison](../../../run1-rule-selection-equality-fix-20261024/validation/flow-taint-patterns-20261024/summary-analysis.json).
- [Validated summary ownership and map entries](../../../run1-rule-selection-equality-fix-20261024/validation/flow-taint-patterns-20261024/mat-summary-bindings-v2/receipt.json).
- [Covered static target matrix](../../../run1-rule-selection-equality-fix-20261024/validation/flow-taint-patterns-20261024/static-covered-targets.json).

Early reports retain failed empty-histogram/owner-selection queries and quoting
errors. They are not labeled wholly validated. The comparison uses individually
validated nonempty component queries, exact full ownership bindings, complete
map/header/trie controls and the corrected validated map-entry report. Zero
global categories follow by subtraction from the independent total histogram.
No failed query is interpreted as a successful coverage measurement.

No new speedup is measured. The evidence supports testing summary-level work
removal and residual batching on Thingsboard **run-1**. It does not establish
a global 90.46% saving or a two-times engine improvement.
