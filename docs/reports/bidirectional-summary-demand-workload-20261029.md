# Summary delivery and demand lookup: workload investigation

Date: 29 October 2026. Production core is unchanged from the
[16 GiB campaign](bidirectional-repeat-run1-16g-performance-20261029.md).
The new repository code consists of small tests. No convergence or
performance fix is included.

The isolated thingsboard counter run identifies a large algorithmic
multiplier in run-2. Of 3.99 million popped static-composition states,
3.74 million have a fixed output mark that cannot match the current
initial. The algorithm still traverses predecessors after these
rejections. It makes 930 million composition attempts and 1.75 billion
reachability checks. Almost all provided summary packets have one leaf.

Summary transport has a separate multiplier. Thingsboard run-1 expands
54.9 million replay candidate packets, then rejects 37.8 million. Conductor's
focused profiles also place substantial work in replay and delivery.
The project-specific results below distinguish these costs from point
admission under call-flow stages.

## 1. Scope and latest iterations

The primary measurements use FULL marks, statics and aliases enabled,
16g heaps and field limits `1,1,2,3,...`. The production tree hashes still
match the measured runtime `c2bc5e78dfdb13f95bda970c5f4e0c247acbac29`.
The saved baseline and primary project campaigns were not rerun for the
small tests or the focused profile readers.

| Primary project | Latest reached | Latest complete | Accepted forward | Outcome |
|---|---|---|---|---|
| OWASP | run-12 | run-11 | run-11 | TIMEOUT |
| conductor | run-4 | run-3 | run-3 | TIMEOUT |
| thingsboard | run-2 | run-1 | run-1 | TIMEOUT |
| Stirling-PDF | run-6 | run-5 | run-5 | TIMEOUT |

The [embedded data](data/bidirectional-summary-demand-workload-20261029.json)
contains the new test evidence, counter derivations, source bindings and
focused reader results. Sample shares below are inclusive Java execution
sample shares. They overlap and are not wall-time shares or operation
counts.

## 2. Small OWASP cycle

[OwaspDemandCycleTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/OwaspDemandCycleTest.kt)
reduces the observed cycle to one helper argument and one String model
field. All helper transfers have STAR tails. The real AP operations create
the ANY/DEMAND result.

```text
main: sink(helper(sourceAll()))

helper model:
    p.*       -> bytes.*
    p.H.*     -> bytes.*
    bytes.*   -> out.*
    bytes.*   -> out.H.*
    out.*     -> ret.*

Forward selected relation:  p.* / FLOW -> ret.[any] / FLOW, DEMAND
Backward coarse route:     ret.* / FLOW -> p.[any] / FLOW, DEMAND
Next initial admission:    p.[any] / FLOW demand -> p.* / FLOW initial
```

Every engine completes through run-9. The selected relation is identical
at runs 5, 7 and 9; the actual handoffs after runs 5 and 7 are equal. Both
production stop checks permit continuation. Only the test policy cap stops
run-9. A precise NORMAL backward `ret.* -> p.H.*` record also exists.

The control removes only the named storage routes. It reaches, completes
and accepts run-3, then stops with NO_DEMAND_EDGE. The full reproducer
reaches, completes and accepts run-9. This is a bounded regression test for
repeated refinement, not an unbounded test or a new stop policy. See
[the detailed fact trace](bidirectional-owasp-demand-convergence-20261029.md#9-small-executable-reproducer).

## 3. Focused profiles change the priority

A new reader splits the closed primary recordings at exact source-method
boundaries. Six windows from four recordings pass fresh controls and hash
checks. All Java samples have stacks; none are truncated. Conductor and
Stirling totals agree with the earlier independent reader.

| Window | Samples | Summary replay | Delivery | C2 initial lookup | C5 summary restriction | Diagonal borrow | Point admission |
|---|---:|---:|---:|---:|---:|---:|---:|
| conductor run-4, whole | 25,431 | 31.71% | 11.69% | 2.38% | 3.04% | 14.86% | 14.37% |
| conductor run-4, middle 30 s | 177 | 0% | 99.44% | 0% | 0% | 0% | 19.77% |
| conductor run-4, late 30 s | 634 | 52.05% | 0% | 2.05% | 1.26% | 40.54% | 8.83% |
| thingsboard run-2, whole | 38,206 | 2.55% | 1.69% | 29.49% | 47.13% | <1% | 1.24% |
| Stirling run-6, whole | 48,987 | 8.11% | <1% | <1% | <1% | <1% | 62.10% |
| OWASP run-10, whole | 10,801 | <1% | 2.72% | <1% | <1% | <1% | 40.59% |

Conductor changes behavior within run-4. The middle window contains input
candidate selection in 22.60% of samples, exact satisfaction in 15.25% and
AP summary application in 16.38%. In the late window, publication candidate
expansion appears in 42.90%, output decoding in 41.17% and diagonal borrow
in 40.54%. The diagonal method is the leaf in 28.23%. These nested shares
must not be added.

Thingsboard's C5 cost is mainly `StaticPairLookup.walk`: 47.02% of all Java
samples, compared with 47.13% for C5. The final `restrictRaw` selector has
only 0.23%. C2's leaves include call-graph `Reachability.reachesAny` in
3,589 samples, `HashMap.putVal` in 2,571 and `HashMap.resize` in 1,817.
C5's leaves include mark classification, list suffix/equality and overlap
inside closure traversal. This supports removing graph work before tuning
these small helpers.

Stirling's broad call-pipeline share does not mean equivalent pub-sub
overhead. Call-flow stages appear in 81.81%, while point admission appears
in 62.10%. The latter contains protection-mask intersection and memo lookup.
The call-flow method handles stages before and after the callee; it is not
only a return suffix. OWASP run-10 also has substantial point-admission
work. The current pub-sub focus is well supported for conductor, and the
demand focus for thingsboard. It does not explain all later Stirling work.

## 4. Summary pipeline and repeated selection

The current pipeline already deduplicates stored inputs and publications:

```text
Raw method summary delta
    -> restrict with fixed demand
    -> pending method publication batch
    -> SummaryStorage: merge current publications, reject empty delta
    -> notify subscribed caller runners
    -> delivery: select current caller inputs, test, apply summary

New caller input
    -> CalleeSubscriptions: merge current input, reject empty delta
    -> replay: select current summary candidates, test, apply summary
```

The remaining problem occurs before output deduplication. Replay first
finds premise members by base/path. It then expands every current output
group for each candidate premise. Only afterwards does `applyMatch` test
the full premise. The exact test depends on the input, premise and mode,
not on the output group.

[SummaryCandidateWorkloadTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/SummaryCandidateWorkloadTest.kt)
uses the real indexes and AP predicate. It supplies 32 concrete mark
premises at the same position, with 16 output bases per premise. These
different bases keep the outputs in different groups.

| Constructed quantity | Replay | Delivery |
|---|---:|---:|
| Expanded candidate packets | 16,384 | 16,384 |
| Successful matches | 512 | 512 |
| Distinct input/premise pairs | 1,024 | 1,024 |

The current candidate count is `K*K*M`; the required output matches are
`K*M`. Here 31/32 of candidate filters reject their mark. The output fanout
is expanded before rejection. A second test, with one premise and 32 output
groups, returns the same selected input from all 32 repeated filters.
Distinct output applications remain necessary.

```text
Current replay:
    related premise -> expand M outputs -> test same input/premise M times

Work-removal candidate:
    related premise -> test once -> if matched, expand M outputs
```

Real field outputs often pack into one tree. The test does not establish
`K=32` or `M=16` on conductor. It establishes an executable multiplier in
the current algorithm, including a multiplier with only one mark.

Delivery rebuilds candidate snapshots for each publication too. Sharing
selection across equal premise/member publications needs a protocol proof:
callbacks can add inputs between publications. A new input has a replay
that sees the batch already inserted, but FLOW replacement, protected
memberships, ND support, aliases and observations must remain correct.

A third test demonstrates a legal registration/publication order where
delivery and delayed replay apply one logical pair twice. Production
replay is Inline, and the test uses queued protocol steps to expose the
allowed order. This proves possibility, not its rate in the project runs.

`DiagonalRelations.borrow` has a separate source-confirmed search: it
knows the exact canonical initial, but scans all header scopes before
testing that initial. All scopes belonging to other initials are unrelated
work. The conductor late-window profile supports investigating this path.

## 5. Initial lookup runs after caller input rejection

`enterCallees` performs these calls in order:

```kotlin
subscribe(Subscription(callee, ref, facts.layer, facts))
link(callee, ref, facts.layer, facts)
```

Subscription admission is synchronous. It can reject the input as already
held, but its Unit return does not prevent the following LinkIn. The
callee still limits the input and runs C2.

Let `Q` be processed LinkIn calls and `A` all accepted subscription deltas.
Every processed link has one preceding subscription call. `A` also counts
zero-only subscriptions and accepted subscriptions whose links have not
yet run. Thus `max(0,Q-A)` is a conservative lower bound on processed links
whose matching caller subscription admitted no delta.

| 16g phase | Processed links Q | Accepted deltas A | Rejected-subscription links, at least |
|---|---:|---:|---:|
| conductor run-4 | 10,254,004 | 5,875,334 | 4,378,670 / 42.70% |
| thingsboard run-2 | 3,048,127 | 3,583,037 | No useful lower bound |
| Stirling run-5 | 2,065,402 | 1,662,369 | 403,033 / 19.51% |
| Stirling run-6 | 1,127,763 | 744,864 | 382,899 / 33.95% |

Reentrant replay and queued links do not invalidate the bound. They can
only increase the accepted-subscription upper bound. The table does not
classify all remaining links as useful or redundant.

Passing only admitted input deltas to callee emission could remove this
work without adding an input-history store. It needs a proof that limit
and initial emission distribute over the exact input union. Keep caller
subscriptions, replay and protection growth. Preserve DEMAND input
presence, all tail/exclusion rules and run-2 static completion. Run-1
requests need their own proof. No link is suppressed in this change.

C2 returns many already admitted initial keys. For conductor run-4 it has
10,254,004 calls, 5,023,432 returned keys and only 201,266 fresh initials
from all admission paths. At least 98.04% of C2 calls create no new initial;
at least 4,822,166 returned keys repeat an existing initial. These are
conservative bounds, not an exact duplicate-query or cache-hit rate. An
empty-result query is included in the first bound. Interrupted queries
are included too; the bounds describe observed work before cancellation.

## 6. Demand lookup: local packet scans and run-2 closure

Local C5 first unions the row IDs related to all output leaves. It then
passes the entire raw packet to restriction for each selected paired row.
`restrictRaw` enumerates every scalar output leaf again. The index's
leaf-to-row association is lost.

```text
Raw:       p.* -> {ret.f0.*, ..., ret.fK-1.*} / FLOW
Demand:    K paired rows, each (entry=p.*, exit=ret.fi.*)
Exit trie: K relevant leaf/row pairs
Current:   K whole-packet restrictions, each scanning K leaves
Result:    K outputs
```

[DemandCandidateWorkloadTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/DemandCandidateWorkloadTest.kt)
checks widths 1, 4, 16 and 64 against the scalar reference. It measures K
production restriction calls, K relevant indexed pairs and K outputs. The
full reference performs `K*K` scalar attempts. The production inner
`K*K` count follows from its source loops; the public counter does not
measure those inner attempts. A protected-TAINT variant checks output
protection too. Protection transport can run the ordinary operation a
second time for the protected subset.

This is a real local query hazard. It is not the dominant sampled cost in
thingsboard run-2: the static closure walk dominates there.

Run-2 C5 sends every traversed static state through restriction, including
intermediate endpoints whose base cannot match the raw packet. Such a
state may still be a required bridge; skipping its restriction is different
from pruning traversal. A stronger candidate uses the fixed right endpoint:
left composition cannot repair incompatible right-endpoint geometry, or
an incompatible output mark once that mark is fixed. FLOW prefixes must
remain eligible until composition fixes the mapped mark.

Run-2 C2 also repeats call-graph eligibility work. Each local/visible view
is new; its visible reachability scratch is new and belongs to that view.
Repeated queries can traverse the same fixed call graph again. A future
reuse design needs an ownership and memory bound. A mutable cache placed
inside the shared immutable demand snapshot is not an authorized fix.

The new counter diagnostic below measures these rejection rates and packet
widths. It confirms the graph priority; the local packet-scan test remains
a checked hazard for other shapes.

## 7. Actual thingsboard operation counts

One isolated run uses the same thingsboard project, FULL mode, 16g heap,
static and alias settings, `1,1,2,...` schedule and 1,080 s analyzer budget.
It calls Gradle `runProjectAnalyzer`. The outer limit remains 1,200 s.
It reaches run-2, completes run-1 and accepts run-1, then stops on TIMEOUT
in run-2. There is no OOM or new heap capture.

The detached source patch adds numeric counters at existing loops. It
keeps the transfer, matching, traversal, publication and stop decisions.
It retains no facts, paths or join histories. Eleven fresh controls and
twelve existing differential/pipeline/driver tests pass. An independent
source review also passes. The actual JVM arguments and compiled classes
are bound to the patch.

JFR and async sampling are disabled for this counter run. Automatic guard
and JVM OOM heap policies remain enabled. Its times are diagnostic context,
not a matched performance comparison. Counter overhead and arrival order
can change how far an interrupted engine proceeds.

### 7.1 Run-1 replay, delivery and writer binding

| Actual run-1 operation | Count |
|---|---:|
| Input subscription offers | 10,493,283 |
| Fresh subscription admissions / replays | 8,196,656 |
| Rejected unchanged subscription offers | 2,296,627 |
| Replay geometric premise members | 17,529,947 |
| Replay expanded packets / exact filters | 54,927,858 |
| Replay filters accepted / rejected | 17,094,201 / 37,833,657 |
| Delivered publication members | 1,151,648 |
| Delivery input snapshots / exact filters | 43,405,435 |
| Delivery filters accepted / rejected | 3,122,434 / 40,283,001 |

Replay rejects 68.88% of the packets after expansion. Delivery rejects
92.81% of candidate inputs after snapshotting. A rejected candidate is not
a duplicated stored fact: the work precedes admission of any output.

One exact filter per geometric premise member would use at most
17,529,947 replay filters instead of 54,927,858: 37,397,911 fewer, or
68.09%. The selected input is independent of the output group. Matching
before decoding would also avoid constructing the 37,833,657 packets for
rejected premises. This is an operation-count bound for the proposed
query-local reordering; no speedup is measured.

Joined writer binding performs another 222,523,224 candidate-input visits,
with 28,030,029 matches. These are outside the normal replay/delivery
filter counts above. Its two writer rows can share one nonstatic initial:

```java
set(p) {
    C.a = p;
    C.b = p;
}
```

```text
Writer rows: p.* / FLOW -> C.a.* / FLOW
             p.* / FLOW -> C.b.* / FLOW
```

Both rows select the same caller inputs for `p.*`. Each output application
is required; repeating selection per static conclusion is a separate
work-sharing candidate. `JoinedStaticWriterBinding.offer` requires a
nonstatic original. Recursive caller-bound writers can arrive later, so
grouping and memory bounds need a dedicated design before changing this
phase.

### 7.2 Run-2 demand and composition

These are the operation totals up to timeout. Started and partial queries
are included; they are not completion rates.

| Actual run-2 operation | Count |
|---|---:|
| C2 queries / scalar actual leaves | 2,408,534 / 3,792,362 |
| C2 emit checks / rejected checks | 8,618,817 / 2,934,505 |
| Returned C2 initial keys | 1,571,893 |
| C5 queries / scalar raw leaves | 145,284 / 146,689 |
| C5 paired offers / scalar restriction attempts | 4,152,830 / 4,226,544 |
| C5 accepted scalar cells | 150,706 |
| BFS state admission attempts | 66,407,200 |
| New / duplicate state admissions | 4,008,283 / 62,398,917 |
| Popped states | 3,992,093 |
| Fixed mapped-output-mark failures | 3,741,361 |
| Static predecessor expansions | 3,089,063 |
| Expansions after fixed entry rejection | 2,893,937 |
| Composition attempts / successes | 930,415,459 / 66,241,306 |

In 99.72% of C5 queries, the raw packet has one leaf. Scalar restriction
has only 1.018 scalar attempts per offered pair. The packet-scan multiplier
from the small test is therefore not this phase's main cost.

The main observed waste is earlier. A fixed mapped output mark fails the
current initial in 93.72% of popped states. Of the static predecessor
expansions, 93.68% occur after that fixed entry rejection. The counter does
not attribute each of the 930 million composition attempts to a specific
rejection class, so these state percentages are not a claimed percentage
of removable CPU time.

For example, a backward FLOW initial cannot satisfy this marked entry:

```text
Provided backward original: ret.* / FLOW
Frozen guidance state:      C.f.* / T -> ret.* / T
Offered demand entry:       ret.* / T
Result:                     initial mark check fails

Prepend C.g.* / U -> C.f.* / T:
    C.g.* / U -> ret.* / T   // the right output is still T
    initial mark check still fails
```

Further left composition keeps the mapped right output mark and its
geometry. This entire branch cannot repair the failed entry check.
The run still expands such branches. Rejecting them before traversal is
the first thingsboard work-removal target.

Keep the distinction from an intermediate output mismatch. The diagnostic
records 194,725 static bridge expansions with a current output mismatch
and no fixed-entry rejection. Prepending a writer can repair that left
endpoint. These states cannot all be pruned by the same rule.

### 7.3 Repeated call-graph eligibility

| Actual run-2 graph operation | Count |
|---|---:|
| Reachability scratch factory entries | 365,239 |
| New graph-instance/root IDs | 1,910 |
| Repeated-root scratch entries | 363,329 |
| Expanded vertices | 905,957,561 |
| Examined edges | 2,050,447,072 |
| `reachesAny` calls | 1,752,166,069 |
| Owner-membership tests | 4,853,181,179 |
| C2 vertex expansions / edge visits | 749,680,441 / 1,692,818,615 |
| C5 vertex expansions / edge visits | 156,277,120 / 357,628,457 |

Repeated scratch roots alone do not prove a full repeated tour. The
vertex and edge counts measure actual traversal. Empty-owner queries are
zero in this run; an empty-target special case would not explain it.

The fixed graph has 51,953 vertices and 117,581 edges. With 1,910 queried
root IDs, at most 99,230,230 distinct root/vertex pairs can occur, compared
with 905,957,561 visits. At least 89.05% of vertex visits repeat a pair.
The corresponding conservative bound for repeated immutable root/owner-
family questions is 98.21%. These bounds support reuse of graph answers;
they do not prescribe a global cache representation.

C5 alone calls `reachesAny` 1,697,456,250 times in 20,621 reachability
scratch contexts. Many checks occur after an owner was already reached
or after the traversal exhausted its pending work. Reusing owner-family
eligibility within one query view is a second work-removal target. Reuse
across views can also avoid repeated root tours, but needs a separate
ownership and retention bound.

The frozen snapshot has at most 16,414 owner-family objects: 14,449 bridge
labels and 1,965 projected entries. Each visible view has one lazy scratch.
Thus at most `20,621 * 16,414 = 338,473,094` distinct view/family checks
are possible in C5. At least **1,358,983,156 checks, or 80.06%, repeat the
same family in the same view**. This bound needs no retained join history.

The source also gives a small correctness argument for query-local reuse.
A true reachability result leaves an owner in the monotone seen set; the next identical
query returns at the initial seen check without changing traversal state.
A false result exhausts pending traversal; the same query remains false
and cannot advance it. The outside-graph test is constant for that view.
A finite source-model control checks result and state equality for 524,288
three-query sequences. A production memo, its storage bound and its formal
integration proof remain for the next design step.

## 8. Next design targets

The [implementation draft](../design/bidirectional-summary-demand-workload-implementation-20261029.md)
specifies the selected first two targets and their demand-rewrite dependency.
Its new formal checks are not new project measurements. A closed EXACT
application case still needs a behavior decision.

The [next-iteration proposal](../design/bidirectional-next-demand-work-20261029.md)
now specifies the first two directions. It places them after the selected
one-step demand rewrite: prune impossible fixed-entry C5 branches, then reuse
query-local owner-family eligibility. Cross-query root reuse remains a later
design step. No production optimization or new project run is included.
The latest thingsboard measurement still reaches **run-2**, completes and
accepts **run-1**. The proposal includes constructive Lean models and a
staged comparison with the future post-rewrite reference.

| Priority and scope | Current work | Candidate behavior | Required preservation |
|---|---|---|---|
| First: thingsboard run-2 C5 | Expand states after a fixed mapped-output-mark rejection | Reject incompatible fixed endpoints before owner lookup, composition and queue insertion | Preserve FLOW prefixes and required left-endpoint bridges; use full mark-group compatibility |
| Second: run-2 eligibility | Repeat owner-family checks and root tours | Reuse query-local eligibility; then assess bounded reuse across queries | Same reachability result and incremental state; fixed method/view scope; bounded memory |
| Parallel target: summary replay | Expand all outputs before the same full premise filter | Match the premise once, then expand required outputs | Same input snapshot, tails, exclusions, protection, ND members and observations |
| Initial emission | Send a full callee input after caller admission rejects it | Emit from admitted deltas while retaining caller subscriptions | Limit/emission union law, DEMAND input presence, run-2 completion, separate run-1 request proof |

Delivery grouping, joined writer selection and unrelated diagonal-scope
search remain measured or source-backed candidates. Their project benefit
must be tested separately. The current evidence identifies large operation
counts to remove; it does not establish an achieved twofold speedup or
authorize an implementation change.

## 9. Validation and evidence

All nine selected tests pass: the two OWASP cases, three summary workload
cases, three demand workload cases and the existing DemandLink regression.
The latter checks a different case where an input DEMAND contribution is
necessary and later refinement removes it. The new tests do not change
that contract.

Run from `core`:

```sh
JAVA_HOME=/usr/lib/jvm/temurin-17-jdk-amd64 ./gradlew \
  :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.OwaspDemandCycleTest \
  --tests org.opentaint.dataflow.bidi.SummaryCandidateWorkloadTest \
  --tests org.opentaint.dataflow.bidi.DemandCandidateWorkloadTest \
  --tests org.opentaint.dataflow.bidi.DemandLinkTest --console=plain
```

The tests assert results and operation counts, not elapsed-time thresholds.
Their constructed cardinalities are not claimed as project distributions.
The first summary-probe attempt used undeclared fixture mark names and
failed before the measured operation. It was corrected to the existing
fixture namespace; production rule declarations were not changed.

The counter diagnostic preserves all 5,089 strict finding identities and
all 92,016 occurrences from the primary accepted thingsboard run-1 report.
Raw instruction/location occurrence counts also match. Both reports keep
run-1 because run-2 is incomplete. This is an observation-preservation
check for instrumentation, not a proof of complete-analysis equivalence.

The focused reader uses at most 2g and two CPUs. Its synthetic controls,
exact method predicates, source/class hashes, window boundaries and all
counts are embedded. The reader's `call-suffix` tag means the whole
call-flow method. A timestamp wrapper correction reused the already
completed conductor output; it did not rerun that reader.

After all profile readers closed, 13 prior raw profile files were removed
after hash and open-handle checks: 944,320,969 logical bytes. Compact
results, source controls, logs, SARIF and numeric memory curves remain.
The cleanup receipt supersedes earlier raw-profile availability statements.
