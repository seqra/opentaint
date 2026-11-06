# Next iteration: lazy loop observations and sparse demand programs

Status: **A, B and C are UNSELECTED. No implementation is authorized by this
proposal.** The measured runtime is `4182adae6152b4600a5401b78512b2b5b581998f`.
The aim is to avoid repeated query work while keeping the current decisions.
There is no promised wall-time factor or claim that forward run 5 is fixed.

The [project report](../reports/bidirectional-demand-guidance-retention-performance-20261106.md)
records the configured attempts and their limits. The current source/measurement
ledger is embedded in the [portable project evidence](../reports/data/bidirectional-demand-guidance-retention-performance-20261106.json),
SHA256 `93550742067888f1269f3a1468ef3a9e514a669b0b98164c045064630a532d14`.
It records exact input hashes, JSON key paths, method contexts, source excerpts
and the counter qualifications used below. Its numeric field-ID examples are
bounded samples, not a complete typed fact trace.

## 1. Rank and semantic boundary

| Rank | Proposal | Operation to remove | Main limit |
| --- | --- | --- | --- |
| A | Evaluate enclosing loop results only when needed | Saved matching, application and enclosing C5 for decisions already determined by complete C2 admissions | Actual joint eligibility is not measured; the main F5 owner has a much smaller marginal bound |
| B | Finalize only touched C5 output programs | Query-local array initialization and visits to programs with no selected input | The prepared-only empty-program fraction is not measured |
| C | Canonicalize a frozen joined input once | Repeated normalization of the same immutable row during static binding | Requires annotated idempotence, exact ownership and repeated-visit counts |

Keep the selected FLOW/DEMAND/ANY guide correction. Do not remove its coordinates
to reduce work. Keep scalar C2, its image, layers, C5 eligibility and budgets,
field transfer, matching roles, protection, complete ND joins, physical ports,
loop growth and stopping. Do not change Facts/Initial equality or add a global
result cache, raw history store, grounding support or speculative cleanup.

P0 is still open: the shared-loop program completes run 5 with zero reports and
fails its expected finding assertion. The complete root capture has 143/143 B2
trace events, three whole snapshots and zero drops. At AL `(3,7)`, its captured
entry is `s.ANY/T -> ZERO`, exit `-2`; a control exit does participate in C2.
The captured concrete C5 offer is already coarse. The later all-method capture
has 12 whole snapshots and seven mapper trace events, with zero drops.
The final point diagnostic locates the actual earlier rejection: call
application preserves `s.f.ANY/T DEMAND`, then point 5 in scope `(3,-2)`,
full original ZERO, rejects it after `s.ANY/T DEMAND` was stored. Transaction
11 has the exact offer, identical whole buckets before/after, and no fresh
delta. `TaintGroup.addAll` returns from `subtractSubsumed` before warm
canonicalization. The diagnostic has 173/173 events, nine complete point
transactions, 12 whole snapshots and zero drops. FLOW-to-TAINT conversion
preserves the child. These scopes and executions must stay distinct.
This evidence does not select a concrete-TAINT guide-retention rule, a new
Target rule or a loop-growth change.
The four conditional mechanism tests do not recover the program. A–C preserve
the current restriction result; they do not claim to repair that coverage gap.

### Required correctness follow-up: concrete demand positions

This is a separate semantic decision before A–C acceptance. The selected
FLOW repair kept concrete TAINT compaction unchanged. The new actual
transaction shows that this boundary is insufficient for the shared-loop
program. It is the concrete counterpart of the FLOW guide-loss mechanism.

```text
Current concrete point admission:
  stored s.ANY/T D; offer s.f.ANY/T D -> no fresh position
  later C2 sees only s.ANY/T and can accept the same cut as the raw fact

Proposed guide contract, subject to the pending behavior decision:
  retain both explicit DEMAND/ANY positions and their actual mark T
  same-coordinate repeat -> no delta
  fresh child after parent -> child delta
  parent after child -> retain both positions
  keep STAR admission and NORMAL data canonicalization unchanged
```

The current native C2 controls show that `s.f.ANY/T` distinguishes
`s.f.g.$/T NORMAL` from `s.f.ANY/T DEMAND`; the root guide does not.
The complete code and trace are in the project report. There is no end-to-end
recovery result for the proposed extension.

Do not implement this as a point-only special case. First specify and prove
the cold packet, early freshness, warm state, packed adapter, summary,
publication, handoff and demand-view contracts. Preserve complete P and
paired ports, field exclusions, full marks, layers and protection. Keep
ordinary and protected channels separate. Equal-point header joins require
an operational C2/request equivalence proof; denotational prefix coverage
alone is insufficient. No new scalar C2 cell or field-transfer rule is selected.
The existing FLOW proof and four conditional tests do not prove these paths.

Add an actual transaction regression and both arrival orders. Then run the
shared-loop program through natural convergence and require its normal
finding. Repeat both repaired prefix cases and the default native gates.
The project campaign must use the new committed runtime if this extension
is selected. Do not relabel the existing `4182adae6` measurements as results
for that unimplemented extension.

The guide correction also changes the work presented to later runs. In the
recorded F3 frontiers, Conductor outgoing demand memberships/method keys change
from `12,986/634` to `174,269/660`; Stirling changes from `701/142` to
`4,682/146`. The analysed-method counts stay 7,282 and 3,696 respectively.
These are membership counts, not unique paths or a proof that every extra row
is required. Old Conductor R4 completed in 6.424 s; current R4 times out after
943.985 s. Cost comparisons must state this changed work and completion status.

## 2. Current measured opportunity

These are disjoint sampled Java scopes in the selected continuous recording.
Allocation percentages use estimated allocation-sample weights, not retained
heap. Inclusive frames and nested scope percentages must not be added.

| Window | Status | Java sample denominator | Loop-observer samples | Observer allocation share |
| --- | --- | ---: | ---: | ---: |
| Conductor R4, backward | TIMEOUT | 108,237 | 65,562; 60.57% | 51.96% |
| Stirling R4, backward | COMPLETE | 11,167 | 8,800; 78.80% | 85.60% |
| Stirling F5, forward | TIMEOUT | 16,269 | 13,342; 82.01% | 88.15% |

The observer includes saved replay, summary application and enclosing C5. Its
whole share is not avoidable work. Ordinary current-delivery scope is below 3%
in these windows. Local `BlockSummaryLinks` already caches native matches per
input group and selected initial. Ordinary publication matching is therefore
not a priority here, despite a separate source-level repetition opportunity.

## 3. A — lazy enclosing loop observation, UNSELECTED

### Current and proposed decision

`LoopOutputRestriction.restrictScalar` first computes the full raw observation.
It then tests emptiness, asks for the first certified budget and tries cuts.
`LoopConsumerObservation.observe` does enclosing saved replay/C5 before it
returns repeat admissions and labels. In contrast,
`LoopRestrictionSession.certifiedFirstBudget` reads only labelled admissions.

For one scalar and the same frozen query context, write the full signature as:

```text
O(v) = (AL(v), E(v), RPT(v), labels(v))
C(v) = (AL(v), RPT(v), labels(v))
```

`C` is complete adjacent/repeat C2 admission, including every scope/family label
and admitted layer. `E` is the complete enclosing DATA/Target set. It includes
whole original P, scope, physical exit, exact geometry, layer and protection.
The word cheap is relative; it does not mean an approximate C2 query.

| Current | Proposed |
| --- | --- |
| Compute `C(raw)` and `E(raw)` before knowing whether a proper trial exists | Compute complete `C(raw)` first; keep `E(raw)` lazy in this scalar call |
| Full observation for every tested cut | Compare complete `C(cut)` first; a difference already rejects equality |
| Every surviving trial repeats enclosing work | Compute full `E(raw)` at most once, then full `E(cut)` only for cheap-equal cuts |

If `C(raw)` is nonempty, the full baseline cannot be empty. If depth is at most
one, or a valid certificate rejects every proper budget, returning the existing
raw scalar needs no enclosing query. If `C(raw)` is empty, full `E(raw)` is
still required: E can be the sole reason to retain the scalar.

### Review sketch

The names below describe a query split, not selected new runtime types. Reuse
the existing immutable views and `LoopAdmissionBundle`. Its adjacent and repeat
queries must both finish before exposing the complete cheap tuple.

```kotlin
fun restrictScalar(raw: Facts, query: FrozenLoopQuery): Facts? {
    checkpoint()
    val cheapRaw = query.completeAdmissions(raw) // AL, RPT, all labels
    val enclosingRaw = localLazy { query.completeEnclosing(raw) }

    if (cheapRaw.isEmpty && enclosingRaw.get().isEmpty()) return null
    val depth = currentBoundedDepth(raw)
    if (depth <= 1) return raw // Nonempty baseline was established above.

    val first = session.certifiedFirstBudget(raw, cheapRaw.labels) ?: 1
    check(first in 1..depth)
    if (first == depth) return raw // No remaining proper trial.

    for (budget in first until depth) {
        checkpoint()
        val cut = existingScalarLimit(raw, budget)
        val cheapCut = query.completeAdmissions(cut)
        if (cheapCut != cheapRaw) continue
        val fullRawEnclosing = enclosingRaw.get()
        val fullCutEnclosing = query.completeEnclosing(cut)
        if (fullCutEnclosing == fullRawEnclosing) return cut
    }
    return raw
}
```

The current certificate signature can take the complete labels directly; it
does not require a full `LoopObservation` with a fake empty E. Construct the
observer/views before asking for precision cursors. Keep all current certificate
guards: STATIC, non-counted paths, missing cursors and unsupported shapes use
the existing fallback. No certificate is evidence that E itself is empty.

For example, suppose an existing frozen interface admits
`arg0.header.value.EXACT/T NORMAL` in an adjacent scope. Its scalar has counted
depth two. A valid certificate of two shows that the proper depth-one MAY cut
adds a different labelled DEMAND admission. Current code computes enclosing
results, performs no trial and returns raw. The proposed code returns the same
annotated raw scalar without E. This is an illustrative decision, not a trace
claim about a sampled production field ID.

For an actual trial, differing labelled admissions already imply
`O(cut) != O(raw)`. If the complete cheap tuples agree, compute both complete
enclosing sets before accepting. Do not stop at the first nonempty family, a
matching count, or one matching enclosing result.

### Count limits

The source counters give marginal certified-zero-trial candidates, before the
required joint `C(raw) nonempty` test:

| Method/context | Window | Marginal candidate bound | Qualification |
| --- | --- | ---: | --- |
| Conductor `ParametersUtils.replaceList`, HashMap argument | R4 | 32,874,543 | Interrupted-scalar slack 1; raw fallback counter is 32,874,544 |
| Stirling `decodeMimeHeader`, StringBuilder argument | R4 | 3,086,928 | Complete owner counters; no interrupted slack |
| The same Stirling owner | F5 | 0–422,054 | Interrupted-scalar slack 1; joint cheap-positive count unknown |

For the complete R4 Stirling owner, shallow nonempty scalars are
`6,581,098 - 0 - 5,854,174 - 0 = 726,924`. Trials equal cuts, so its certified
zero-trial count is `3,813,852 - 726,924 = 3,086,928`. Conductor's aborted sample
needs its balance/slack qualification. These are bounded method samples, not
global counts. They do not prove fast-path eligibility. In particular, A alone
is not shown to remove Stirling F5's dominant observer work.

### Law, scope and tests required

Prove in Lean, for the same frozen context:

```text
C(v) nonempty                         -> O(v) nonempty
C(cut) != C(raw)                       -> O(cut) != O(raw)
C(cut) == C(raw) and E(cut) == E(raw)   <-> O(cut) == O(raw)
valid certificate c                  -> every budget < c rejects full equality
lazyRestriction(raw)                  = eagerRestriction(raw)
```

The last equality concerns the exact annotated result, including drop versus
raw versus the first accepted cut. Retain current whole-packet canonicalization,
scalar order, growth/ND classification, limits and bypasses. Queries must remain
read-only over the same full-P/scope/exit/policy views; no requests, rules,
subscriptions, sources or static effects execute during observation. Saved
direct/opposite reads and each enclosing query keep their native visit order.
Lazy state ends with this scalar call, not the work quantum or run.

Native checks must cover C-only, E-only, both empty, conflicting AL/RPT, equal
unlabelled sets with different labels, protection-only differences, ND P, both
saved directions, targets, STATIC/non-counted fallback, certificate-at-depth,
and cancellation. Preserve every existing cut/drop decision on a bounded
reference corpus. A complete-observation diagnostic must force all four parts
or clearly mark E as uncomputed; it must not print uncomputed E as empty.

Count complete cheap queries, cheap-positive raw queries, certificate/no-trial
queries, their **joint eligible count**, cheap-different trials, E(raw)
materializations, E(cut) materializations, accepted cuts, drops and raw returns.
This measures the removed work instead of estimating it from marginal totals.

## 4. B — sparse output-program finalization, UNSELECTED

### Current and proposed handling

`PreparedOutputPrograms.intersect` uses its output trie to select program
ordinals. It allocates `arrayOfNulls(programs.size)` and creates a bucket only
after `restrictConclusionOnly` selects a value. It then scans **all** programs,
including every null bucket, before packing and limiting selected programs.

Keep the immutable program list and trie. Replace only query-local bucket
storage/finalization with sparse ordinal buckets and an ascending touched list.
Do not pack each selected scalar separately or merge outputs across programs.

```kotlin
val buckets = sparseOrdinalMap<ProgramBucket>()
val touched = mutableOrdinalList()
var references = 0
var overflow = false

forEachDemandScalarInExistingOrder(raw) { protected, scalar ->
    outputTrie.visitNativeOrder(scalar) { ordinal ->
        if (!overflow) {
            checkpoint()
            val program = programs[ordinal]
            val selected = restrictConclusionOnly(scalar, program.fullExit)
            if (selected != null) {
                val bucket = buckets.getOrPut(ordinal) {
                    touched.add(ordinal)
                    ProgramBucket()
                }
                if (bucket.stream(protected).add(selected)) {
                    references++
                    if (references > 2048) overflow = true
                }
            }
        }
    }
    !overflow
}
if (overflow) return null // Native fallback; no partial output escaped.

for (ordinal in touched.sortedAscending()) {
    checkpoint()
    val program = programs[ordinal]
    for (packet in existingPackProgramStreams(buckets[ordinal])) {
        existingLimit(packet, program.fieldBudget, result)
    }
}
return result.all()
```

Keep the existing entry-ticket capability, complete original templates, scope,
policy and exact paired exit. The program key remains `(fullExit, fieldBudget)`.
All Reach/ZERO/template/domain/absent-base guards stay in their current order.
Protected selection is still visited first; each stream keeps its native header,
insertion order and mark/exclusion/protection content. The exact reference cap
is still `> 2048`, with the same duplicate rule in each stream.

For example, a plan has 10,000 programs but one packet selects only ordinals
9,001 and 4. Current code initializes 10,000 slots and tests every final bucket.
The proposed code stores two buckets, then finalizes 4 and 9,001 in that order.
It uses each program's original full-exit budget. Selection order is not used
as output order. This is a plan example, not a measured touched fraction.

Let n be program count, k be touched nonempty buckets, and t be trie candidate
visits. Current fixed work is O(n) initialization plus O(n) finalization. The
proposed fixed work is expected O(k) sparse storage plus O(k log k) ordinal sort.
The t visits, exact restrictions, packing and field cuts remain. In a successful
query, k is at most the existing 2,048 selected-reference bound. Plan construction
still costs O(n). A dense query can gain little or pay extra map/sort cost.

### Evidence and missing denominator

| Window | Mixed `c5RowAttempts` | Mixed exact rejects | Mixed ratio | Prepared queries / trie candidates |
| --- | ---: | ---: | ---: | ---: |
| Conductor R4 | 3,620,680,565 | 3,353,003,323 | 92.6070% | 70,888,786 / 267,716,512 |
| Stirling R4 | 313,599,658 | 157,578,213 | 50.2482% | 28,521,552 / 180,288,476 |
| Stirling F5 | 2,347,095,605 | 2,168,381,261 | 92.3857% | 26,732,866 / 183,755,095 |

These totals combine native C5 and prepared paths. They are **not** the measured
null-bucket fraction, and cannot be multiplied by an enclosing CPU share to
predict a saving. Add separate prepared counters for n, visited candidates,
null restrictions, distinct touched programs, empty programs, finalized programs,
selected references, pack calls, cuts and fallback reasons. Preserve bounded
row samples with clear new meanings. Skipping null rows changes diagnostic
attempt/sample counts; do not silently compare them to the old mixed counters.

### Law and tests required

Prove that dense bucket i and sparse bucket i have the same two ordered selection
sets; an absent sparse bucket is exactly a null dense bucket. Sorting touched
ordinals is the old program order with no-output programs removed. Thus the
ordered packed/limited outputs and final annotated result are equal. Prove the
same overflow point and native fallback, with no partial output publication.

Native tests need no touched program, one/two programs, dense selection, duplicate
members, protected-only and mixed streams, distinct E/tails, full ND originals,
distinct budgets for similar exits, scalar/trie order different from ordinal
order, exactly 2,048 and 2,049 references, cancellation and every existing
native fallback. Compare full outputs and layers, not counts alone.

## 5. C — frozen joined inputs once, UNSELECTED

Thingsboard times out during run-1 static completion. In its recorded derived
static-completion window, canonicalization has 12,806 of 25,725 Java samples
(49.78%) and 51.57% of allocation weight. The 341.194 s window is reconstructed
from logs; it is not a new native stage clock. The event envelope reports no
missing prefix/suffix, which does not prove uniform sampling or no internal
gaps. Not all canonicalization work is repeated or removable.

The [existing frozen-input proposal](bidirectional-frozen-inputs-no-cut-work-next-iteration-20261105.md#2-canonicalize-frozen-joined-inputs-once)
audits the source route. Moved local/caller input directories canonicalize on
visits; the joined static binder can canonicalize again before matching.
Two writers such as `C.f = p.value; C.g = p.other` can visit the same fixed
caller row. Keep each complete premise match and writer application.

```text
Current: each visit -> canonicalize owned raw input -> match -> apply writer
Proposed:
  adopt the existing directory, without normalization
  release execution
  first joined visit: Raw(value) -> complete canonical packet list -> Ready(list)
  later visits:      Ready(list) -> same ordered packets -> match -> apply writer
```

Replace the owned row payload after complete success, under its existing stable
handle. Do not update a temporary snapshot, keep a second raw copy, add a global
cache or normalize during detach. An unvisited row pays no normalization cost.
The row must be immutable after ownership transfer, including protection.
Keep complete caller P/context, scope, ports, group, zero-only mode and order.
Caller candidate postings may stay a conservative superset; exact matching
still uses the canonical current packet. No new local candidate index is needed.

For frozen row i, let visits be v_i and normalization cost be a_i. The targeted
work changes from roughly sum(v_i * a_i) to sum(a_i for visited i), plus the
same packet visits and applications. Count distinct rows, repeated visits,
actual normalizer calls and allocation weight before estimating impact.

Prove ordered annotated idempotence `C(C(value)) = C(value)`, including protection;
ordinary Facts equality is insufficient. Prove no post-transfer updates, exact
owner/key preservation, safe conservative candidate selection and closure of
all adopted Raw/Ready rows. Ready is installed only after the full list exists.
Cancellation/failure keeps the old owned state or closes the failed joined
phase; no partial export is committed. Replacing a payload does not prove that
shared DAG nodes are freed. Keep the existing lease and release boundary.

Test local and real-call rows, one/many writers, unvisited rows, multiple packet
headers, ZERO, pre-transfer protection upgrades and cancellation before/during/
after first use. Compare complete bound writer effects and next-run demand.

## 6. Proof and experiment gate before selection

Follow the [proof guide](../../spec/proof-guide.md). First model the lazy decision,
sparse ordinal result stream and frozen ownership law constructively in Lean.
The current 39 guidance lemmas do not prove A, B or C. Then use native reference
tests at the exact adapters above. Any required change to admission, layers,
growth, Target support, transfer or stopping is a separate behavior decision.

Measure A, B and C separately before a combined run. A and B overlap in enclosing
C5 work, so their expected savings cannot be added. Record joint eligibility,
per-query n/k, visited/finalized programs, and frozen-row revisit counts; retain
bounded failure and zero-work cases. Attribute CPU/allocation to exact windows,
including `canonicalFlowDataPacket` in normalization. Keep disjoint scopes and
inclusive frames separate, and keep allocation churn separate from retained heap.

After selection and implementation, repeat the same four configured projects:
direct `runProjectAnalyzer`, FULL, 16 GiB, `1,1,2,...`, aliases/statics on and the
saved project budgets. Reuse f945/52f/8331 controls; do not rerun them. Report
strict identities, censoring, OOM/timeouts, run-1/transition/later costs and
reached/completed/accepted labels. Keep the initial infrastructure-failed
Conductor attempt separate. Do not claim a factor-of-two saving, a repaired F5,
or quality acceptance from sample shares or a shorter timed-out prefix.
