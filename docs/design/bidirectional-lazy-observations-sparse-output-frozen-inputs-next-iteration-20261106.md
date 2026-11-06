# Next iteration: lazy observations, sparse outputs and frozen inputs

Status: **proposal only; A–D are not selected or implemented.** The measured
runtime is `7069fe2d73a32443d98163fc67970a3114983712`. This proposal removes
repeated pure query work while preserving the current annotated results. It
does not promise a speedup factor or repair the remaining getter finding.

The [current performance report](../reports/bidirectional-protected-guidance-storage-performance-20261106.md)
and its [portable evidence](../reports/data/bidirectional-protected-guidance-storage-performance-20261106.json)
carry the configured project results. The earlier
[4182 proposal](bidirectional-lazy-loop-observations-sparse-demand-programs-next-iteration-20261106.md)
is historical. Its counts and candidate bounds must not be used as current
measurements. No old baseline is rerun for this proposal.

## 1. Rank, current status and semantic boundary

| Rank | Candidate | Work to avoid | Evidence limit |
| --- | --- | --- | --- |
| A | Make enclosing loop observation lazy within one scalar query | Saved-record application, enclosing C5 and result union when admissions already decide the result | Joint eligibility is not yet counted; E-only scalars still need E |
| B | Finalize only touched C5 output programs | Allocate/scan no bucket for programs with no selected input | Current reject ratios mix native and prepared paths; the touched fraction is unknown |
| C | Reuse each exact normalization stage of a frozen joined input | Recompute the same packet list for different static-writer visits | Repeated visits and memory cost need measurement; no global canonical confluence assumption |
| D | Prepare immutable C2 path-budget metadata at its query owner | Count the same path's fields again for each row/actual comparison | Hot leaf samples show cost, not the number of redundant scans |

C is the first project-specific candidate for Thingsboard static completion.
A and B have the strongest evidence across Conductor and Stirling. D is a
narrow follow-up; it does not replace the larger work-avoidance candidates.

All project tables below use **R/C/A** for latest reached / fully completed /
accepted forward report. A run END or BARRIER_END alone does not prove commit.

| Current project | Terminal status | R/C/A | Relevant completed or interrupted phase |
| --- | --- | --- | --- |
| OWASP | COMPLETE | 5/5/5 | Natural run-5 completion; no broad late-loop hotspot established |
| Conductor | TIMEOUT | 4/3/3 | F3 complete, 213.835 s engine; R4 interrupted, 787.973 s engine |
| Stirling-PDF | TIMEOUT | 5/4/3 | R4 complete, 390.893 s engine; F5 interrupted, 614.349 s engine |
| Thingsboard | TIMEOUT | 1/—/— | Run-1 engine 518.580 s, then static completion 425.523 s; no accepted forward report |

Keep literal H coordinates, effective EXACT identity, same-header span E, and
selected DEMAND/ANY guide positions. Keep STAR admission, scalar C2 and its
image, field counting/cuts, NORMAL/DEMAND layers, full marks and exclusions,
matching roles, complete ND execution, scope/physical ports, loop growth,
Target rules, static authority, report acceptance and stopping. Do not change
Facts equality/hash, infer protection from overlap, merge different originals,
or add a live/global cache. Proof of a pure rearrangement does not authorize a
different semantic contract.

The [saved-record capture](../reports/bidirectional-getter-saved-record-gap-20261106.md)
keeps the small getter finding OPEN: its complete pre-F3 getG directory has no
saved NORMAL return relation. C2 rejection at the later boundary is partly
source-derived, not a logged rejected-C2 callback. A–D preserve this policy;
none claims program recovery or a final Conductor missing-finding cause. Root
owns the separate native probes and any admission-policy decision.

## 2. What changed in the work

Both Conductor F3 executions below analyse 7,282 nonzero method keys. `4182`
is a historical control, not the current runtime. These counts show changed
work, not just a slower primitive at a fixed workload.

| Conductor F3 measure | Historical 4182 | Current 7069, R/C/A 4/3/3 |
| --- | ---: | ---: |
| Engine seconds | 61.863 | 213.835 |
| Outgoing demand edges / method keys | 174,269 / 660 | 257,270 / 668 |
| Processed packet events | 1,109,383 | 2,642,300 |
| Fresh post-store packet events | 1,543,912 | 4,061,125 |
| Candidate offers | 1,153,676 | 3,792,169 |
| Block candidate offers | 878,548 | 3,100,048 |
| Prepared C5 queries | 4,338,445 | 12,909,257 |
| Prepared C5 trie candidates | 11,796,590 | 27,491,889 |
| C5 limit calls, mixed routes | 10,734,558 | 25,044,809 |

The selected retention contract requires explicit guide positions to survive.
The increased frontier is consistent with more guidance reaching later work.
These aggregates do not prove which extra row is required, nor identify every
producer. Do not prune those positions to recreate the old count. First avoid
queries and full scans whose results cannot change the current decision.

Current F3's combined summary census has 18,412 admitted concrete output
memberships and 7,781 outgoing concrete memberships. Protected memberships are
zero in both combined totals, including public and block components. Combined
FLOW output annotations are 297,035 admitted / 259,784 outgoing. These census
units differ from frontier demand edges: do not subtract one from another to
invent an exact FLOW edge count. Both the sampled and retained-summary evidence
give no support for H-wrapper/E-family work as the cause of this F3 increase.
This is not proof that no protection exists anywhere in the process.

| Current sampled window | R/C/A | Java samples | Loop observer samples / share | Observer allocation share | Sampled H-owned stacks |
| --- | --- | ---: | ---: | ---: | ---: |
| Conductor F3 | 4/3/3 | 19,280 | 6,627 / 34.37% | 36.63% | 0 |
| Conductor R4 | 4/3/3 | 191,271 | 122,762 / 64.18% | 48.56% | 0 |
| Stirling R4 | 5/4/3 | 12,069 | 9,482 / 78.56% | 86.46% | 7 |
| Stirling F5 | 5/4/3 | 18,345 | 15,003 / 81.78% | 87.92% | 1 |
| Thingsboard static completion | 1/—/— | 31,445 | 0 / 0% | 0% | 0 |

These are disjoint Java sample scopes, not CPU seconds. Allocation shares use
estimated sample weights, not retained heap. The observer share contains useful
work and is not an avoidable-cost estimate. Conductor F3 also has C5 scope
3,138/19,280 (16.28%) and canonicalization 2,238/19,280 (11.61%). Its
`RestrictedInitialPolicy.fitsBudget` leaf is 2,520/19,280 (13.07%). These leaf
and nested scopes overlap; do not add them.

Current R4 conditional observer internals include saved-record application
73,641/127,489 observer-containing samples, enclosing C5 15,863 and C2 admission
12,983. This conditional partition includes stacks assigned another outer
disjoint scope; 127,489 is not the disjoint 122,762 observer denominator above.
Stirling F5 saved application is 9,606/15,405 observer-containing samples, also
separate from its disjoint 15,003 observer count. This supports
avoiding a complete enclosing evaluation when it cannot affect the answer.
It does not establish how often that condition holds.

Logged method leaders also changed. Conductor F3 now has
`ForkJoinDynamicTaskMapper.getDynamicTasksSimple` at 5,227,704 observations,
`ParametersUtils.replaceList` with HashMap context at 3,726,610, and
`replaceVariables` with HashMap context at 3,485,170. Their 4182 counts were
756,513, 1,789,959 and 1,689,788. Current R4's leading logged owners are instead
`ParametersUtils.replace` with HashMap context, 29,806,319; virtual
`Map.replaceAll` with the `ParametersUtils.getTaskInputV2` lambda context,
22,616,851; and `WorkflowExecutorOps.decide`, 9,892,714. R4's logged-only
observation denominator is 76,182,108. These are bounded owner counters,
not a census of all methods or an identity between method and profile samples.

One actual current F3 C5 sample, `WorkflowExecutorOps.decide` at route 0, says:

```text
matchingMember var(11):[10440,6128]/STAR/FLOW/mx[]/E[]
Dc             var(11):[10440]/ANY/FLOW/mx[]/E[]
Dp             <this>:[17448]/ANY/FLOW/mx[]/E[] ; budget 2
raw            ret:firstBranch[13768]/ANY/DEMAND/maxFL1/protectedfalse
selected=null ; admitted=null
```

This sample establishes one concrete no-output finalization: the entire raw
Facts packet has base Return, while Dp has base This. Every raw coordinate has
that packet base, so no path catalogue or complete branch list is needed for
this base mismatch (`Reference.kt:240` rejects unequal bases). This exact
method/context has 3,170,364 prepared queries,
zero native queries and zero reference fallbacks in complete F3. In the prepared
kernel, `sampleResult(null, null)` is emitted by null-bucket finalization.
The plan's coarse `outputs.hasBase(Return)` guard can succeed because another
program has Return base; the dense final loop still visits this This program.
B would skip that no-output program without changing any restriction result.

The first-branch path remains incomplete. Numeric fields have no catalogue
here; whole P, physical scope and ports are not reconstructed from this sample.
It proves one unnecessary program finalization, not a full producer chain,
whole-query emptiness or a global touched/null-program fraction.

## 3. A: delay complete enclosing observation

Current source computes adjacent admission, saved matching/application,
enclosing C5 and Target results, then repeat admission and labels before it
returns. `restrictScalar` needs full nonemptiness first, then the certificate,
then equality for the first acceptable proper cut. The certificate reads
labelled admissions only.

For one frozen full-original/scope/port/policy context, define:

```text
C(v) = (adjacent admitted initials, repeat admitted initials, labelled admissions)
E(v) = complete enclosing DATA and Target results
O(v) = (C(v), E(v))
```

C is complete, not an approximation. E retains original P, scope, physical
exit, effective pattern, layer and literal protection. A nonempty family is
not permission to omit another family when equality is still required.

```kotlin
fun restrictScalar(raw, frozenQuery): Facts? {
    checkpoint()
    val cRaw = frozenQuery.completeAdmissions(raw)
    val eRaw = localLazy { frozenQuery.completeEnclosing(raw) }
    if (cRaw.isEmpty && eRaw.get().isEmpty()) return null
    val depth = existingScalarDepth(raw)
    if (depth <= 1) return raw
    val first = existingCertificate(raw, cRaw.labels) ?: 1
    if (first == depth) return raw
    for (budget in first until depth) {
        checkpoint()
        val cut = existingScalarLimit(raw, budget)
        if (frozenQuery.completeAdmissions(cut) != cRaw) continue
        val eBaseline = eRaw.get() // Preserve baseline-before-cut E evaluation.
        if (frozenQuery.completeEnclosing(cut) == eBaseline) return cut
    }
    return raw
}
```

Illustration: a scalar has depth two, complete C is nonempty, and the current
certificate rejects budget one. Current code still computes E(raw), performs
no trial and returns raw. A returns the exact same annotated raw value without
E. For a tested cut whose complete C differs, both versions reject it; E(cut)
is unnecessary. If C(raw) is empty, E(raw) is mandatory because E can be the
only support. Compare cheap C before materializing E on each trial; this second
case matters where the no-trial bound is small, including Stirling F5.

Current counters provide only marginal no-trial candidates:

| Current owner/window | R/C/A | Certified no-trial marginal | Joint eligible count |
| --- | --- | ---: | --- |
| Conductor F3 `getDynamicTasksSimple`, default context | 4/3/3 | 874,023 | Unknown, between 0 and marginal |
| Conductor F3 `replaceList`, HashMap context | 4/3/3 | 945,566 | Unknown, between 0 and marginal |
| Stirling R4 `decodeMimeHeader`, StringBuilder context | 5/4/3 | 3,126,313 | Unknown, between 0 and marginal |
| Same Stirling owner, interrupted F5 | 5/4/3 | 0–435,743 | Unknown, at most marginal bound |

For the two complete Conductor F3 owners, trials equal
`certificateFallbacks`; every uncertified deep nonempty scalar needs at least
one trial. Thus no certified scalar takes a trial. Certificates give the two
marginals. For complete Stirling R4, shallow nonempty scalars are
`6,611,557 - 0 - 5,887,297 - 0 = 724,260`. Trials equal accepted cuts, so no
failed trial ends raw. Subtract shallow values from raw fallbacks:
`3,850,573 - 724,260 = 3,126,313`. For F5, shallow count is 6,425 and raw
fallback count 442,168; failed trials prevent identifying the no-trial subset.
None of these counts tests C(raw) nonempty. Do not substitute the 4182 bounds.

Constructive proof obligations for a finite exact observation model:

1. A witness in any C component gives a witness that O is nonempty.
2. A differing C component witnesses unequal O, regardless of E.
3. Equal C and equal complete E are equivalent to equal O.
4. The unchanged certificate supplies a rejecting admission witness for every
   earlier proper budget. Keep all current unsupported-shape fallbacks.
5. Induct on the ordered budget list. Each candidate is rejected or accepted at
   the same first budget; empty, raw and cut results, layer and H agree.

These are constructive finite product/list laws, not an assumption that E is
empty. A formal model must include the current complete annotated observation
keys and certificate witness. This document supplies the proof design, not a
checked Lean result. Queries must be read-only over the same frozen context.
No requests, rules, subscriptions or static effects may be delayed/skipped as
if they were pure observations. Keep whole-packet canonicalization before
scalarization, growth/ND classification, STATIC/non-counted fallback, all saved
directions, Target handling and cancellation checkpoints.

Reuse the existing admission bundle so adjacent/repeat queries and their labels
are complete without duplicate label queries. Construct the same observer/views
before asking for precision cursors: current `MethodBlockRuntime` obtains them
from the observer map populated by `observe`. Splitting the call must not turn
an uninitialized observer into a missing-certificate fallback. Keep E(raw)
before E(cut) whenever both are evaluated, and keep native order within each
saved/query stream. Lazy state ends with this scalar call.

Required native differential cases: C-only, E-only, both empty, conflicting
adjacent/repeat labels, identical unlabelled initials with different scope or
layer, H-only differences, ND originals, both saved directions, Target-only,
STATIC/non-counted cursors, certificates at depth, and every accepted-cut
position. Compare exact annotated outputs and first accepted budget. A trace
must say E was uncomputed; it must not print uncomputed E as empty.

## 4. B: finalize touched output programs only

`PreparedOutputPrograms.intersect` already selects candidate ordinals with a
trie. It still allocates `arrayOfNulls(programs.size)` and visits every program
after selection. A null bucket performs row statistics/sample work and rejects.
The source demonstrates an avoidable O(n) pattern, but not its measured null
fraction or the cost of each atomic increment.

Keep candidate visitation, exact paired-entry capability, output templates,
`(fullExit, fieldBudget)` keys, protected-first stream order, selected-reference
deduplication and the strict `> 2048` fallback. Change query-local storage and
finalization only:

```kotlin
val buckets = sparseOrdinalMap<ProgramBucket>()
val touched = ordinalList()
existingScalarAndTrieVisit { protected, scalar, ordinal ->
    val selected = existingRestrict(scalar, programs[ordinal].fullExit)
    if (selected != null) {
        val bucket = buckets.getOrPut(ordinal) { touched.add(ordinal); ProgramBucket() }
        existingStreamAddAndReferenceCap(bucket, protected, selected)
    }
}
if (existingOverflow) return null // no partial output escapes; native fallback
for (ordinal in touched.sortedAscending()) {
    checkpoint()
    existingPackBothStreamsAndLimit(buckets[ordinal], programs[ordinal])
}
```

A plan with 10,000 programs that touches only 4 and 9,001 finalizes those two
in ordinal order. It still packs each complete program stream before cutting;
it does not cut scalars separately or combine different programs. Dense
selection can gain little or pay map/sort overhead.
The actual Return-versus-This sample in section 2 is a measured instance of a
skippable program. Sparse finalization skips every other-base program and any
same-base program with no selection, while retaining the original whole-P
capability, paired exit, scope and budget for every touched program.

| Current window | R/C/A | Prepared queries / trie candidates | Mixed exact rejects / row attempts |
| --- | --- | ---: | ---: |
| Conductor F3 | 4/3/3 | 12,909,257 / 27,491,889 | 287,817,457 / 312,862,266 = 91.99% |
| Conductor R4 | 4/3/3 | 79,356,293 / 221,223,310 | 4,306,545,244 / 4,527,471,271 = 95.12% |
| Stirling R4 | 5/4/3 | 28,648,609 / 181,149,108 | 158,366,203 / 315,014,887 = 50.27% |
| Stirling F5 | 5/4/3 | 27,704,412 / 189,239,522 | 2,227,345,799 / 2,411,424,395 = 92.37% |

`DemandStore.intersectAt` also writes `dataRow/rejectedRow`. These ratios mix
native/fallback and prepared paths and are **not** a prepared empty-program
fraction. They must not be multiplied by a profile share to predict a gain.
R4's `PreparedOutputPrograms.intersect` leaf has 29,423/191,271 samples
(15.38%); it includes more than null scanning. Allocation/sample counter costs
are not isolated by that leaf.

For n programs, k touched nonempty programs and t candidate visits, change
fixed query work from O(n) initialization plus O(n) finalization to expected
O(k) storage plus O(k log k) sorting. Retain t exact candidate restrictions,
packing and limits. A successful query's k is bounded by the existing selected
reference cap. Plan building still visits all native row occurrences.

Constructive proof: induct over the unchanged scalar/trie event sequence.
Each dense bucket equals the corresponding sparse bucket, including the two
ordered selection sets. Missing sparse buckets equal null dense buckets.
Reference counts and overflow occur at the same event. Filtering the ordinal
list to nonempty buckets preserves old finalization order; removed buckets
emit nothing. Hence packed/limited annotated outputs and fallback agree.
Do not silently change diagnostic meanings: count total plan width and actual
finalized width separately, and name skipped null-program/sample work.

Native gates: empty, one/two touched and dense queries; ordinal order different
from selection order; duplicates; H-only and mixed streams; full marks, E,
tails and layers; whole ND original; similar exits with different budgets;
2,048/2,049 references; all native fallbacks and cancellation. Compare complete
annotated outputs, not just counts.

## 5. C: reuse frozen input normalization at the same stage

Thingsboard static completion contains 15,087/31,445 canonicalization samples
(47.98%) and 52.45% of estimated allocation weight. The phase lasts 425.523 s.
Within canonicalization, inclusive `canonicalTaintPacket` has 15,033 samples;
these are a margin within the same samples, not an additive scope. Sampled H
ownership is zero in this phase. The separate run-1 engine window has
13,903/78,212 H-owned samples (17.78%); it is not evidence that H dominates
static completion. Continuous recording begins about 106 s after run-1 starts,
so engine-window proportions are partial coverage.

`CalleeSubscriptions.visitJoinedCandidates` normalizes a current input for
each writer visit. `LocalInputDirectory.candidates/visitCanonical` does the
same for local inputs. `OwnedJoinedStaticWriterBinding.complete` can normalize
the supplied packet again before matching/application. These are different
stages: do not remove the second stage by assuming canonical idempotence.

```kotlin
// Owned only by this joined, immutable input directory.
class FrozenInputStage(val exactRowHandle, val exactRawValue) {
    val packets = localLazy { existingCanonicalPackets(exactRawValue) }
}
for (writer in existingOrder) {
    for (row in existingConservativeCandidates(writer)) {
        for (packet in row.sameStage.packets.get()) {
            existingMatchAndBind(writer, row.owner, row.fullOriginal, packet)
        }
    }
}
```

Example: the same frozen caller row is selected by 100 writer visits. Current
code computes K(raw) 100 times at that directory stage. C computes that exact
ordered annotated packet list once and reuses it for those 100 visits. A later
stage K(packet) remains unchanged, or gets a separate exact-stage memo only
after its own purity/ownership proof. No input-only cache may merge full P,
link, scope or layer. This does not change candidate selection, real ZERO
authority, summary role, matching, writer queue order or onBound effects.

Constructive law: for an immutable x and deterministic read-only K, store the
first computed list as a witness `cached = K(x)`. Every later read returns
that same ordered list. Induction on visits preserves all callback arguments
and order, hence outputs. This needs no equation
`C(C(X) union Y) = C(X union Y)` and no global DATA normal-form confluence.
It does not allow moving normalization across release/ownership boundaries,
across a new row version, or from joined state into live delivery.

Expected reduction is from v normalizations to at most one for each selected
frozen row at the specified stage. Actual v and the distinct row count are
not measured. The retained packet lists can increase live memory; release them
with the joined directory and measure their peak bytes/count. Do not replace
this lifetime rule with a global weak/result cache. Native tests need repeated
writer visits, untouched rows, exact same-prefix H with distinct E, DEMAND/ANY
positions, mixed marks, same geometry/different full originals and scopes,
normalization stages that differ, zero-only input, close/release and cancellation.

## 6. D: prepare exact C2 budget metadata, after A/B measurement

The current `fitsBudget` leaf counts a Pattern path on each call. Immutable
demand templates and repeated actual leaves can repeat that scan in one frozen
query owner. Prepare counted depth for the exact pattern once at that owner;
reuse it only for the same path and field limit. Keep every existing guard,
normalization, catalogue-dependent mark check and emitted-initial legality
test. A cut or different path needs its own depth. Do not substitute raw path
length for counted fields, particularly STATIC and Element/class accessors.

The constructive law is structural induction over the path list:
`preparedDepth(path) = count(isCounted, path)`. Thus each reused comparison
`preparedDepth <= limit` equals the current guard. Lift this only through the
unchanged C2 branch tree and same immutable query key. The source-derived
same-head ANY/STAR rejection remains rejection. Full initializer shape/layer
checks remain mandatory. Measure path scans and reuse counts before claiming
work avoided; 13.07% leaf samples are not an eligible-work fraction.

## 7. Proof-first acceptance and experiment plan

Follow [the implementation proposal guide](../../spec/impl-proposal-guide.md)
and [proof guide](../../spec/proof-guide.md). Before implementation, build
constructive finite models with executable counterexamples and no `sorry`,
classical choice or new axioms. Model the current and proposed algorithms
separately, prove annotated result equality within the stated frozen scope,
then prove the distinct work bound. Refine any failed native/model bridge;
do not weaken literal H, guide or role contracts to make a proof pass.

Run each selected candidate separately against committed 7069 under identical
configured FULL memory/time/field/alias/static/IR/worker settings. Root owns
builds, handles, measurements and postprocessing. Do not rerun f945 or 52f.
Use the prepared native proof/test gates before the configured project rerun.
Keep the unresolved getter assertion visible, together with its inherited
control result; do not call native storage success global finding recovery.

Record these new operation counts with exact owner/window coverage:

| Candidate | Required counts before an impact claim |
| --- | --- |
| A | Complete C queries; C-positive raws; certificates at depth; **joint C-positive/no-trial** eligibility; cheap-different trials; E(raw)/E(cut) materializations; saved applications/C5 calls avoided; drops/cuts/raws |
| B | Query n; candidates t; selected references; distinct touched k; finalized programs; actual null restrictions; packing/cuts; fallback reason and exact cap point |
| C | Frozen row/version count; selected visits v; per-stage K calls and reused lists; packet/member counts; retained-cache peak and release; exact output equality |
| D | Counted-path traversals; prepared-pattern count; reuse hits; unchanged emitted cells/layers; unsupported-context fallback |

Repeat end-to-end finding identity comparisons, latest R/C/A, completed F3
frontier/census and packet work, engine and barrier times, timeout/OOM status,
selected per-run profiles, and memory evidence. Compare equivalent completed
phases; interrupted R4/F5 totals are censored. Report both fixed-work reduction
and any changed time left for later work. One new recording, changing demand
volume, GC occupancy or sampled allocation does not prove a retained-memory
cause, a twofold speedup or full quality. No fresh heap/OOM artifact exists in
this campaign.

After a selected change lands, capture bounded exact facts at the affected
producer/query boundaries: full original, scope/entry/exit, actual input,
admitted initials, complete output/H/guide coordinates, and the explicit skip
reason. Bind every skip count to its exact offered-query denominator. Where a
producer chain is not completely observed, leave it unproved. Current counters
do not prove why each extra guide is necessary, and first-branch samples must
not be promoted into full causal chains. New diagnostics are observational;
they cannot change the gate or remove required guidance.

## 8. Exact evidence and source ledger

External evidence root **R** is
`canonical-relations-directional-inside-20261105/preparation/concrete-guidance-storage-campaign-20261106`.
Its `analysis-tools/postprocess/root-postprocessing-completion.json` binds all
nine files below. This review read JSON/source only and verified those nine
hashes; it did not read raw JFR/heap files or run an analyzer, JVM or profiler.
The performance report's portable JSON embeds the current derived evidence.

| `R/analysis-tools/postprocess/derived/` file | SHA256 |
| --- | --- |
| root-causal-review.json | `1a347ec528124d29bc27796ea449a1b7254d8b99579af6a989f48944e65b5232` |
| workload-log-census.json | `0da8e4164f7f39165cb11443413ff6c7549198caff4b65e5c95319b2b8deb9d5` |
| iteration-census.json | `90bc0c82c1eea309f1ced0b8b938bde74b22b62f2ed9e413988420a0e63f84ef` |
| normalization-opportunities.json | `1dc682f4b77af1755ec7cd7c851fb3b78077e0de4de8e9234eeb94ccc094d594` |
| protected-wrapper-review.json | `11f7a4936a6d64ee7419f2b3175896cd6af62b4b2cfcbc1fd6bf3a0ca01c5958` |
| profile-hotspot-review-20261106.json | `f9843f68f5891c518dbd7d9b88a7882d48deb4c1d987184a412e8d4bd874f4a6` |
| final-profile-bundle.json | `685ffad04ee6522904bced9fd6c68e532fac99da12a114c9d6d80c3785ff9444` |
| campaign-review.json | `b4ad2d13d9578c6984f8e2206b22376a175520abdf5cff07cec97dfc1463517d` |
| quality-comparison.json | `84acd94c5a06d6f8dffb2f3c14d3d30a19a8fa77af9d3fda4399b5489f8d74c4` |

Exact key paths:

- Profiles: `root-causal-review.projects.<project>["run-N"].{samples,scope,leaf,observer_samples,Howned}`;
  Thingsboard phase key is `run-1-static-completion`.
- Counters and marginals: `workload-log-census.projects.<project>.runs["N"].methods[<complete method/context>].counters`;
  prepared/mixed counts are `.globalDemandStore.counters`. Method contexts and
  bounded/top-owner coverage are retained there, not inferred from method names.
- F3 packet work: the same run's `BIDI_BODY_WORK_STATISTICS.counters`.
  The quoted C5 sample is `.boundedTextSamples.BIDI_C5_ROW_SAMPLE[0]`.
- Iterations: `iteration-census.projects.<project>.{progress,runs["N"].timingSeconds,runs["N"].frontier}`.
  The retained summary census is the labelled `BIDI_FLOW_BACKED_CENSUS` raw line
  under Conductor F3 `.controls`; repeated labels must not be read through its
  flattened last-value counter map.
- Thingsboard canonicalization: `normalization-opportunities.projects.thingsboard.recordings[0].windows["run-1-static-completion"]`.
- Historical comparison: `campaign-review.projects.conductor.references["4182"]`
  binds the old attempt. Its separate workload source is
  `analysis-tools/guidance-retention-selected-attempts-20261106/readers/derived/workload-log-census.json`,
  SHA256 `a455f3addfcde4bb5a943aae230cf9d992e82ef71d7f07928f2353005bc1f50d`.
  It is used only for the explicitly marked historical columns.

Current source anchors, relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`:

| Source | Lines / reviewed cell | SHA256 |
| --- | --- | --- |
| engine/LoopConsumerObservation.kt | 60–116, complete observer and pure mark-request sink | `c20974a42e87a0f56a0a097a85a34a7900bfef08e71bfc65864e74946195321a` |
| engine/LoopOutputRestriction.kt | 139–203, canonical packet/scalar order and eager baseline | `524c294994fb4632fb1b28d81c26f40857f7c0ab89b97cdee177acc6d6f03435` |
| engine/LoopRestrictionSession.kt | 20–57, label-only certificate | `4cea593d1c6de29b62d49e7ba3f4fa8fcfab353e59c53d5deda3b5ef71021c2f` |
| engine/MethodBlockRuntime.kt | 518 and 771–836, session call and observer/view initialization | `99229571571f0b15b4a02795845d771f76079c55c566920c99b6f1c97ec6ec00` |
| store/PreparedOutputPrograms.kt | 29–90, bucket array, candidate/overflow and all-program finalization | `682b774936ee5cc56857a4d2be79e4ccb59778fb05cc475203f347f403c2a747` |
| store/DemandResultCoverage.kt | 13–80, mixed row/reject and prepared counters | `ade7b5a26ceb3973c60e4a58598256d7ba116b53003e019074816bd74e1cde1d` |
| engine/CalleeSubscriptions.kt | 113–130, joined repeated normalization | `9a6cc4264824789f717bf0f7428e54c69e25ca67313b24d4c22c9564d7fe63f7` |
| engine/JoinedLocalInputs.kt | 46–76, candidates and canonical visits | `64d6b7c943604a7f178c4539dd36702b2243569970fc9bd9e59c63dcd720a101` |
| engine/OwnedJoinedStaticWriterBinding.kt | 69–105, exact writer/input group and further normalization | `1d309b63dd52feebcc11d9c3de086c9b562e7797ca46359fadf306ae6e8f3ae2` |
| ap/RestrictedInitialPolicy.kt | 15–38 and 111–130, unchanged C2/field budget | `dcbaee551ecdae33590c56ef0154bfd0ef419c8c8fa3dc7b38127006a73ad44e` |
| ap/Reference.kt | 237–241, conclusion-only restriction rejects a different output base | `f8a6ee199524b4982ffd8bea7e1f78c9cad45ba8e43c2c522233967f3f26a453` |
| ap/SpatialCanonical.kt | 48–83 and 408–471, selected guide/H packet behavior | `daea564174ac8bd837c70ed4ca3598fd63690686db855047f96810c7318a1608` |

The root completion receipt records two append-only reader corrections: parser
execution binding and the summary lookup key. Original failed reader attempts
are not marked complete. Corrected readers did not change raw measurements,
source/runtime inputs or the nine bound results. These provenance limits apply
to every candidate and table above.
