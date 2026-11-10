# Redundant demand elimination campaign

10 November 2026. This document specifies an investigation and proof campaign.
It does not select or install a production optimization.
Use ASD-STE100 Simplified Technical English for reports and proposals.

## 1. Goal and fixed scope

Classify every repeated outgoing demand edge in these completed forward runs:

| Project | Earlier run | Later run | Field limits under `1,1,2,...` |
| --- | --- | --- | --- |
| OWASP | run-9 | run-11 | 8, 10 |
| Conductor | run-5 | run-7 | 4, 6 |
| Stirling-PDF | run-7 | run-9 | 6, 8 |

**The removal point is after run-(i+2), not after run-i.** Keep run-i and
the intervening analysis unchanged. Use run-i only to establish repetition
and explain its cause. After the later run completes and its NORMAL records
are persisted, test whether its repeated demand edge can be omitted from
the outgoing guidance for the next run. Do not remove current-run effects,
persisted NORMAL records or reports.

Thus, the removal barriers are OWASP run-11, Conductor run-7 and Stirling-PDF
run-9. A predicate does not need to justify removal at the earlier barrier.

For each repeated edge at the later barrier, produce either:

1. A checked predicate and witness that prove the edge is redundant at the
   specified removal point.
2. A faithful code example, native regression test and fact trace that show
   why removing the edge after the later run can lose required analysis behavior.

Repeat discovery alone does not establish redundancy or non-termination.
Unsupported by a predicate does not mean necessary.

The campaign ends only when every repeated edge has this disposition at the
later barrier. No sampled subset or unexplained residual category satisfies
the goal.

## 2. Reference behavior

Start with production runtime
`14d7b63369d94f49d4c551be8405ed7719f267cc`, used by the
[run-11 validation report](../reports/bidirectional-run11-cutoff-validation-20261109.md).
A newer documentation-only HEAD is acceptable when its production tree is
identical. Record both revisions and source/configuration hashes.

Use the existing project preparation, models, extensions, aliases, static
propagation, FULL mode and `1,1,2,...` schedule. The run-11 cutoff remains in
effect. OWASP uses its CI project, 8g and 1000 seconds. Conductor and Stirling
use their saved project configurations, 8g and 1080 seconds. Exact launch
manifests in the reference report take precedence over a paraphrased command.

The reference report reached these iterations:

| Project | Latest reached | Latest completed | Latest accepted forward |
| --- | --- | --- | --- |
| OWASP | run-11 | run-11 | run-11 |
| Conductor | run-8 | run-7 | run-7 |
| Stirling-PDF | run-11 | run-10 | run-9 |

These are historical values, not receipts for a new capture. Every new report
must state its own reached, completed and accepted forward iterations, even
when its tables concern an earlier pair.

Reuse complete compatible captures where available. Otherwise, use a passive
observer and source Gradle `:runProjectAnalyzer`. Run project scans serially
with the pinned configurations. Record capture overhead and finding-location
comparisons. Diagnostic times are not new performance measurements. Do not
combine two executions to construct one run pair. A missing or incomplete
barrier is not an empty demand set.

Production transfer, C2, C5, persistence, matching, report and stop behavior
remain unchanged during corpus capture. Controlled deletion belongs in the
small test cases described below. A production change requires a subsequent
implementation proposal and selection.

## 3. Define the repeated set precisely

For project p, completed forward run r and full method key m, let S(p,r,m)
be the final outgoing demand set owned by m. Then:

```text
D(p,m) = S(p,earlier,m) intersection S(p,later,m)
M(p)   = { m | D(p,m) is not empty }
```

The complete sets S can differ. D is their exact common subset. Dump the
earlier-only and later-only edges too, so additions and removals remain visible.

Include every final edge selected to guide the next run:

- AP summaries on DEMAND, with their complete original premise.
- Other AP summaries selected by the existing handoff rule, such as a NORMAL
  ND summary. Record its real layer and its selection reason.
- Outgoing DemandTarget summaries.
- Method-owned block/loop summaries and Targets selected for handoff. Their
  scope and physical ports stay in the edge identity.

NormalTarget is not outgoing refinement demand. Retain its records as provider
or observation evidence where required. Classify unsupported demand kinds;
do not omit them because P handles only FLOW DATA.

Use final stores after work has joined, deduplication and subsumption have
completed. Do not compare callback streams, raw C5 candidates or only newly
published deltas. Also dump the actual projected next-run demand rows and map
them to their outgoing origins. Scalar edges, packed packets, ND projections
and normalized handoff rows have different counts; reconcile them explicitly.

### Stable edge identity

Expand packed output trees and mark sets into exact scalar memberships. Keep
the full paired relation. Preserve:

- Declaring method, full descriptor, language, context and forward entry.
- Method/block scope and real entry/exit ports. Record the decomposition map.
- Edge kind and actual layer.
- The complete ZERO/singleton/ND premise. Sort an ND set without splitting AND
  into independent premises for comparison.
- Base kind, concrete field path, tail kind, field exclusions, mark slot,
  full mark identity and mark exclusions on both endpoints.
- Separate plain/protected memberships, as the current storage specifies.
- Target kind and all semantic payloads that actually belong to its identity.

Remove allocation IDs only. Keep raw IDs and complete catalogs beside the
canonical form. A catalog must distinguish full accessor identities, including
owner and type; equal short field names do not establish equality. The array
element accessor `[]` must not be confused with a STAR tail. Generated marks
and specialization identities must remain distinct.

Keep the handoff selection reason as metadata. A changed reason does not make
an otherwise equal edge different. Do not add diagnostic provenance to edge
equality. For example, DemandTarget
is anonymous in the core. Its sink locations/rule identities belong in a
separate complete provenance table, not in an invented Target ID.

Group edges by full method key for M. Keep block and port tags inside each
edge key, so similar edges from different boundaries cannot become a match.

## 4. Phase A: dump the entire corpus

For each project:

1. Freeze both completed forward snapshots from one execution.
2. Export every final outgoing edge and its handoff projections.
3. Compute M, D, earlier-only and later-only sets.
4. Export every method in M with its complete D and all relevant contexts.
5. Reconcile counts with the authoritative stores and report counters.

Capture the preceding and intervening backward demands, C2 offers and
initials, C5 inputs/outputs and retained NORMAL records when required to
explain an edge. Include all producers of a merged edge. Capture only a
representative producer for presentation after the complete evidence is saved.

Every stream needs a record count, completion marker, error count and hash.
Detect truncation and dropped records. Preserve canonicalization and decoding
scripts. A tool's successful exit alone is not proof that a capture is complete.

## 5. Phase B: test P at the later barrier

Use [P: NORMAL replay coverage](../../spec/normal-backed-flow-demand-retirement.md)
and its [proof package](../../spec/lean/proposals/normal-backed-demand-20261110/README.md).
Pin their source versions and respect their declared scope and proof limits.

Evaluate P only at each pair's later completed barrier. Use the NORMAL
records retained there, after persistence. A provider first available in the
later run is valid evidence for removal after that run. Keep the earlier
state for the repetition trace; no deletion or P verdict is required there.

For a positive result, save the complete copy/origin relation and every native
replay witness, including scope, direction, direct/opposite role, shared
suffix, exclusions and availability. For a negative or unknown result, save
the first failed guard and the remaining uncovered origins. An unsupported
loop, static, concrete, ND or Target case remains an elimination target.

P is a context-dependent predicate, not a table of edge shapes. Do not infer
it from one matching NORMAL output or from the equal findings count.

Let U contain one target for each repeated edge in the three pairs, at its
later barrier. Initially:

```text
resolved = { X in U | P has a checked certificate at X.laterBarrier }
targets  = U - resolved
```

Each repeated-edge ledger row retains both snapshot references and one
disposition for removal after the later run. If P holds there, the target is
resolved even when P did not hold after the earlier run.

## 6. Phase C: process uncovered targets one at a time

Maintain one ordered, durable work queue and one coordinator. Select one
uncovered later-barrier target and record its ID. Then:

```text
while targets is not empty:
    X = selectOne(targets)
    traceAllRelevantProducersAndConsumers(X)

    if a sound redundancy rule can be established:
        Q = defineExecutablePredicateWithExplicitGuards(X)
        proveAndValidate(Q)
        addVersionedPredicate(Q)
        for Y in allRepeatedLaterBarrierTargets:
            if Y is open and Q has a checked witness for Y:
                classify(Y, REDUNDANT_Q, witness)
        rebuild targets from the ledger
    else:
        case = buildFaithfulNecessityExample(X)
        proveAndReplayRequiredBehaviorLoss(case, removeOnly=X,
                                          after=X.laterBarrier)
        classify(X, NECESSARY_WITH_CASE, case)
        rebuild targets from the ledger
```

"Could not find a redundancy rule" does not authorize the else branch's final
classification. The required necessity example must succeed. Until then X
remains open. If several producers merged into X, analyze every relevant
producer and their interactions.

After accepting each Q, filter the entire remaining corpus before selecting
the next target. Save a witness for each matched target. Shared geometry
alone is not a batch certificate. Re-test all affected rows if a predicate or
proof changes; a refuted proof reopens its assigned rows.

Use clear predicate names. P remains pinned; a wider or different rule gets
its own name, version, declared domain and proof. The rule must be executable
from analyzer state or an explicitly constructible certificate. It cannot be
"drop the edge when it is harmless" or a list of project/method names.

## 7. Acceptance gate for every new predicate Q

Follow [spec/proof-guide.md](../../spec/proof-guide.md). Before declaring Q
accepted, provide:

1. A precise boolean predicate, deletion point and required available state.
2. Current versus proposed behavior, supported scope and explicit exclusions.
3. A constructive Lean model, executable witnesses and soundness proof.
4. A source correspondence argument and native tests of the real operators.
5. Positive examples and counterexamples to weaker versions of the predicate.
6. A proof/validation receipt and per-target certificates at the later barrier.

The proof must cover the required later behavior, not only concrete relation
inclusion. Check NORMAL replay before demand admission, C2/C5, both directions,
source permissions, ZERO/Target routing, rule observations, report identity,
call bindings, aliases, scope/ports and future refinement as applicable.
Preserve complete ND premises, literal protection and all merged producers.
Prove provider retention, arrival-order safety and absence of circular support.
The accepted predicates must remain sound when all their selected edges are
removed from guidance after their respective later barriers. A witness must
not depend on another removed edge unless a
proved replacement chain ends at independently retained state. Save those
dependencies and check them again after each new predicate.

Do not justify deletion with equal counts, one project's unchanged findings,
an unavailable future provider or a raw unadmitted summary. Do not silently
change initial grammar, field transfer, marks, cleaners, matching or report
semantics to make Q pass. Highlight a proposed major semantic change and ask
the user for the intended behavior. Keep affected cases open while a decision
is pending, and continue independent work.

A limited proof is valid only for its exact declared domain. Unknowns outside
that domain stay in the queue. Production implementation and performance
claims are subsequent work; proof-only success is not a landed optimization.

## 8. Acceptance gate for a necessary-edge case

Provide a small code snippet with the source, sink, pass or cleaner rules
needed by the case. Use real instructions and legal fact shapes. Derive the
summaries through the current analyzer; do not inject an impossible initial or
fabricate a summary to force the result.

The example must reproduce the same demand edge at run-i and run-(i+2), with
the intervening backward run. **Require i >= 3.** The earliest valid pair is
run-3/run-5, and the earliest removal point is after run-5. A run-1/run-3
example is not sufficient evidence that a later-run edge is necessary.
Run-1 has special handling that can invalidate predicates for later runs.
Keep the normal run-1 initialization and iteration schedule in the fixture;
do not rename iterations or reset state to meet the minimum index.

The example must preserve the real reason P and every accepted Q fail at
the later barrier. Include its retained NORMAL providers,
replay roles, caller context, exclusions, protection and boundary ports.
Removing a provider which exists in the project does not produce a faithful
counterexample for that project occurrence.

For each relevant run, copy the code and annotate each method or extracted
block as follows:

```java
// Incoming paired demand: ...
// Submitted facts: ...
// Emitted initials and layers: ...
Result method(Input x) {
    // Inline the facts at the instructions that matter.
    return ...;
}
// Produced NORMAL summaries: ...
// Produced DEMAND summaries and Targets: ...
```

Use the code's variables. Show fields after a base. Keep produced summaries
after the complete declaration. Explain any IR temporary explicitly. Include
the earlier/backward/later trace and any further run needed to show the loss.
Record the actual field limits; do not manufacture repetition with a changed
project configuration or impossible fixed limit.

Run two controls from the same fixture and runtime:

- Baseline: the edge repeats at run-i and run-(i+2), with i >= 3, and the
  required modeled behavior is reached.
- Deletion: keep execution unchanged through the later completed forward run.
  Then remove only the selected edge from that run's outgoing guidance,
  no earlier than after run-5.
  Show the first missing required fact, summary, source permission, Target
  route or valid source-to-sink finding, and trace the loss to the outcome.

Loss of an extra MAY combination, a callback count or a spurious provisional
path is not proof that an edge is necessary. A baseline test that already
misses the finding is not a valid deletion control. State the concrete valid
flow or other required semantic observation that is lost.

Link the fixture to the actual project edge and its later barrier. A generic counterexample
which only refutes an unsafe shape-based rule leaves the project edge open.
A case may serve several edges only when each has a checked mapping that
preserves all relevant preconditions and available replacement routes.

## 9. Artifacts and audit ledger

Use one campaign ID and save all final evidence in the repository, for example:

```text
docs/reports/bidirectional-redundant-demand-campaign-<id>.md
docs/reports/data/redundant-demand-<id>/
    manifest.json
    snapshots/<project>/run-<r>.jsonl.gz
    repeated/<project>.jsonl.gz
    methods.json
    p-results.jsonl.gz
    predicate-catalog.json
    predicate-results.jsonl.gz
    ledger.jsonl.gz
    reconciliations.json
    cases/<case-id>/...
    receipts/...
spec/lean/proposals/redundant-demand-<id>/...
```

Dump all results. The report can summarize them, but no top-N limit, sample
or external-only scratch path may replace the complete sets and ledger.
Compressed artifacts must have portable decoders and schemas.

Each ledger entry must identify the project, run pair, full method key,
scope/ports, exact edge key, both snapshot references, the later removal
barrier and verdict, predicate/case ID and version, witness/proof/native-test references,
and any pending issue. Keep an audit log of classification changes.

The manifest must pin the runtime, project revisions, configurations,
rules/models/extensions, observer and decoder sources, source hashes,
commands, completion/error counts, artifact hashes and actual latest reached,
completed and accepted iterations. Save finding-location comparisons and
explain capture differences instead of merging inconsistent executions.

The report must contain:

- The complete M and D inventories, with links to all edge records.
- Totals by project, method, edge kind, layer, mark kind and scope.
- P coverage and failures at each pair's later barrier.
- Every accepted Q, its proof domain and newly covered edge/method counts.
- Every necessary case and its mapped later-barrier targets.
- Final reconciliation of the full repeated universe against the ledger.

Do not interpret the percentage of retired edges as a measured CPU or memory
improvement. No post-implementation speedup has been measured in this campaign.

## 10. Completion and collaboration

Terminal dispositions are `REDUNDANT_P`, `REDUNDANT_<Q-name>` and
`NECESSARY_WITH_CASE`. Unsupported, unknown, proof-pending, reproducer-pending
and decision-pending are nonterminal.

Completion requires zero open targets, every edge in every D accounted
for at its later barrier, all predicate proofs/native checks passing, every necessary
case passing both controls with i >= 3 and removal after run-(i+2), and every
count/link/hash reconciled. Neither a
representative example nor the discovery of one broad Q ends the campaign.

Use subagents for independent capture preparation, decoding and proof or
counterexample review of the current target. The coordinator still processes
new target explanations one at a time and applies each accepted predicate
globally before advancing. Keep measured project scans serial. Preserve the
ledger across turns and resume at the next unresolved later-barrier target.
