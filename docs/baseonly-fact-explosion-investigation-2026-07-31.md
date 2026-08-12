# BaseOnly fact-explosion investigation

Date: 2026-07-31

## Conclusion

“Fact explosion” currently describes four different multipliers:

1. **Intraprocedural path edges.** The analysis state is
   `(method initial fact, statement, current final fact)`, not just
   `(statement, final fact)`. Alternative initial fields and alternative current
   facts therefore form a product at every statement.
2. **Method summaries.** Surviving exit path edges become exact summaries.
   Summary subsumption and field generalization can compact this layer, but only
   after the callee has paid the intraprocedural cost.
3. **Summary dispatch.** Each published summary is routed to caller
   subscriptions. BaseOnly currently broadcasts to every exit in a selected
   base partition and performs the authoritative delta check afterward.
4. **Side-effect-requirement refinement.** Repeated exclusion growth for the
   same requirement is published as a sequence of deltas. Every delta is sent
   to every subscriber, converted back to an initial fact, and re-abstracted
   against all facts already registered for that method.

Summary field generalization is effective at layers 2 and 3. It cannot reduce
layer 1 inside the method being summarized. Two independent policy problems
made the first experiment look ineffective:

1. the production shallow manager did not receive the generalization flag;
2. after correcting the wiring, the threshold of 16 ignored the dominant
   two-member families.

With generalization at the second compatible member, Conductor shallow forward
time falls from 19.708 s to 10.716 s and rule search falls from 38.244 s to
15.028 s. The current implementation is nevertheless unnecessarily expensive:
it rescans a whole summary partition on almost every insertion.

ThingsBoard is dominated by layer 4 instead. F2F field generalization cannot
affect that path. A per-base current-blocker index in initial-fact abstraction
is the first mitigation; it makes the matched shallow run complete in 9.210 s.
Exclusion-update batching remains a second-stage optimization if event and
union costs are still significant afterward.

The safest useful generalization is **conclusion-only widening with an unchanged
premise**:

```text
P -> Q.f1.*
P -> Q.f2.*
...
P -> Q.fn.*

becomes

P -> Q.*
```

This cannot make a new caller fact applicable because `P` is unchanged. Joint
premise-and-conclusion widening is useful too, but it is a separate, more
aggressive operation and needs a fanout guard.

## The four layers

### 1. Intraprocedural path-edge state

`MethodEdgesInitialToFinalBaseOnlyApSet` stores:

```text
initial access
  -> statement
       -> set of final accesses
```

The initial access is the outer map key. There is no coverage join between two
different initials. At a given statement, `statementsWithFacts()` can therefore
show only 20 distinct final facts while the analyzer has hundreds of distinct
initial-to-final path edges.

An exclusion update also republishes every final stored for that initial and
statement. This is a second local multiplier, independent of summary
generalization.

### 2. Exit summary state

`NormalMethodAnalyzer` emits an F2F summary only after a path edge reaches a
normal method exit. `MethodInitialToFinalBaseOnlyApSummariesStorage` then:

1. merges identical exact edges;
2. computes a subsumption antichain;
3. optionally runs field generalization.

Consequently, exit generalization cannot save any work already performed while
the edge traversed the callee CFG.

The current implementation calls `BaseOnlyF2FFieldGeneralizer.rewrite` on the
whole canonical partition after each affected add. Generalization is rare, so
most calls only rescan and regroup edges.

### 3. Summary subscription and application

`MethodBaseOnlyAccessPathSubscription` is currently conservative to the point
of broadcasting:

- Z2F `find` returns every stored exit;
- F2F `find` returns every `(caller initial, caller exit)`;
- ND marks every storage index relevant and returns every exit.

Only later does `NormalMethodAnalyzer.applyMethodAnySummaries` call the
authoritative `tryApplySummaryEdge`. The candidate cost is therefore roughly:

```text
published summary-initial groups × caller exits in the base partition
```

A summary index can remove rejected candidate work. It does not by itself
remove accepted path edges. Conclusion generalization reduces both retained
summaries and accepted downstream results.

### 4. Side-effect-requirement refinement

`BaseOnlySideEffectRequirementApStorage` joins requirements with the same
base/access by growing their exclusion:

```text
base / access / E
    + E-new
becomes
base / access / (E union E-new)
```

Each changed union is emitted as a new requirement delta. For every matching
subscriber, `handleMethodSideEffectRequirement` converts the requirement back
to a caller initial fact. `BaseOnlyInitialFactAbstraction.registerNewInitialFact`
then inserts each newly excluded accessor and re-abstracts every fact already
in `state.added`.

The resulting cost is approximately:

```text
exclusion refinements
  × matching subscribers
  × existing registered facts
```

This is not an F2F-summary path. No setting in
`BaseOnlyF2FFieldGeneralizer` can reduce it.

## Minimal executable reproduction

The existing `BaseOnlySummaryFieldExplosionSample.permuteField` has 20
nondeterministic reads followed by 20 nondeterministic writes:

```java
switch (readSelector) {
    case 0: selected = input.f00; break;
    ...
    default: selected = input.f19;
}

switch (writeSelector) {
    case 0: input.f00 = selected; break;
    ...
    default: input.f19 = selected;
}
```

The experiment ran the same BaseOnly analysis twice and changed only
`summaryStorageFieldGeneralizationEnabled`.

| metric | disabled | enabled |
|---|---:|---:|
| `permuteField` path-edge steps | 65,684 | 65,684 |
| projected helper statement facts, total | 160 | 160 |
| maximum projected helper facts at one statement | 21 | 21 |
| relevant retained helper F2F summaries | 21 | 1 |
| caller path-edge steps | 673 | 613 |
| projected caller statement facts, total | 65 | 25 |
| maximum projected caller facts at one statement | 42 | 2 |
| caller handled-summary batches | 56 | 36 |

Without generalization, the helper retains one identity and 20 field-premise
summaries:

```text
arg(0)          -> return
arg(0).f00.*    -> return.*
...
arg(0).f19.*    -> return.*
```

With generalization, the field family becomes:

```text
arg(0).* -> return.*
```

This is direct evidence of the boundary:

- helper-local work is identical because the summary does not exist until exit;
- retained summaries and downstream caller work are reduced;
- counting only final facts hides the large initial-by-final path-edge product.

## Conductor experiments

The first experiment did not enable generalization in the actual shallow
manager. `TaintAnalyzer.shallowScan` constructs a dedicated
`BaseOnlyApManager(fieldSensitive = true)` independently of the normal
`ApMode.BaseOnlyField` manager. Setting the flag only on the latter changes the
full scan, not the shallow scan.

The corrected experiment enabled the storage flag on the dedicated shallow
manager and compared disabled, threshold 16, and threshold 1. Threshold 1 means
that the second compatible member triggers generalization. All three runs
produced the same six final rule/fingerprint pairs; the threshold 1 run also
retained the same 19 shallow discoveries.

| metric | disabled | threshold 16 | threshold 1 |
|---|---:|---:|---:|
| shallow forward analysis | 19.708 s | 21.157 s | 10.716 s |
| rule search | 38.244 s | 38.264 s | 15.028 s |
| retained F2F summaries | 92,868 | 87,822 | 58,717 |
| groups crossing threshold | 0 | 7 | 5,847 |
| `terminateWorkflow` path-edge states | 95,323 | 79,261 | 25,674 |
| `decide` path-edge states | 56,170 | 36,678 | 19,225 |
| `scheduleTask` path-edge states | 55,676 | 48,430 | 12,891 |
| `DoWhile.execute` path-edge states | 25,947 | 22,050 | 10,675 |
| peak memory | 6.99 GiB | 6.61 GiB | 6.41 GiB |

The abstraction therefore works semantically and reduces downstream state.
The threshold, not the abstraction, explains the apparent failure:

- threshold 16 finds only seven unusually large groups, so the cost of 64,951
  whole-partition rewrites over 341,083 inputs exceeds the savings;
- threshold 1 finds 5,847 groups, reduces stored summaries by 37%, and reduces
  representative hot-method path edges by 66–77%;
- rule search improves because it has fewer summaries and trace states to
  traverse;
- final findings remain equal.

The largest generalized families are generated-code builders and small
constructor/lambda transformations, for example:

```text
Task.Builder.buildPartial0:
    this.* -> return.rateLimitFrequencyInSeconds_.*
    this.* -> return.rateLimitPerFrequency_.*
    ...
    this.* -> return.*

WorkflowTask.Builder.buildPartial0:
    this.* -> return.name_.*
    this.* -> return.taskReferenceName_.*
    ...
    this.* -> return.*
```

These are predominantly conclusion enumeration with the same `this.*`
premise. They are exactly the safe conclusion-only case. Their representatives
then flow into the large workflow methods, which explains why seven local
groups remove thousands of downstream states.

Theoretical group sizes explain why 16 is the wrong threshold. Of 28,786
eligible disabled-run groups:

- 14,560 have one member;
- 12,307 have two;
- only a handful exceed 16;
- the largest groups have 31, 28, 25, and 21 members.

Two alternatives are already enough to create a scalar branch in BaseOnly
where Tree would keep two branches in one access tree. Waiting for 17 members
preserves almost the whole downstream multiplication. The generalizer should
therefore act on the second member and update only the affected group. A
whole-store scan is structurally disproportionate.

## ThingsBoard result

The bounded ThingsBoard run timed out in prescan. That cancellation also
cancelled the persistent analyzer coroutine scope: `Cancellation.Cancelled`
escaped from a child of a plain `Job`, and the following shallow runner launched
its jobs into the already-cancelled scope. Its progress stopped at
`1 / 30,771`; unit queues contained thousands of entries while every unit had
`processed=0`. The final zero BaseOnly counters are therefore accurate for that
broken shallow run, but they are not evidence about field generalization.

This is a separate runner-lifecycle defect. A prescan timeout must not poison
the next phase; the analyzer scope needs a `SupervisorJob` or a fresh scope per
runner. It should not be mixed into the BaseOnly summary-generalization design.

An isolated `SupervisorJob` experiment allowed the real BaseOnly shallow phase
to execute. At shallow +13 seconds:

```text
EntityActionService.pushEntityActionToRuleEngine
    steps: 103,008
    handled summaries: 24,703

AuditLogServiceImpl.constructActionData
    steps: 49,311
    handled summaries: 12,751

DataValidator.validate
    steps: 10,529
    handled summaries: 19,509
```

Heap then crossed 12.85 GiB and high-memory cancellation began. All ten sampled
worker stacks were processing
`SummaryEdgeSubscription.NewSideEffectRequirementEvent`, not F2F
generalization:

- six were registering new initial facts through
  `BaseOnlyInitialFactAbstraction.registerNewInitialFact`;
- four were joining requirement exclusions in
  `BaseOnlySideEffectRequirementApStorage.mergeAdd`.

The source has the matching refinement pattern. `EntityActionService` updates
the same `metaData`/`entityNode` receivers through many branch-specific
`putValue`, `put`, `putArray`, and `addKvEntry` calls.
`AuditLogServiceImpl.constructActionData` repeats this shape in a large switch
over one `actionData` receiver. These branches produce many exclusion
refinements for one structural premise; each intermediate refinement is
republished and replayed.

The evidence proves that ThingsBoard and Conductor have different dominant
explosions:

- Conductor: F2F field-conclusion enumeration and downstream summary fanout;
- ThingsBoard: repeated side-effect exclusion refinement and initial-fact
  re-abstraction.

## Mitigation plan

### 1. Make field generalization incremental

Replace `rewrite(allCanonicalSummaries)` with per-group state:

```text
exact edge key -> exclusion
erasure group -> canonical members or representative
```

An insertion should touch only:

- its exact key;
- its conclusion group;
- if enabled, its joint premise/conclusion group;
- antichain entries that the changed representative can cover or be covered by.

No unchanged group should be regrouped or sorted.

Acceptance gate on Conductor:

- retain approximately the threshold 1 result: at most 58,717 stored F2F
  summaries and the observed 66–77% hot-method state reductions;
- reduce rewrite work to the members of the changed group rather than 341,083
  partition visits;
- shallow forward must remain near or below 10.716 s and rule search near or
  below 15.028 s;
- preserve 19 shallow discoveries and the same six final rule/fingerprint
  pairs.

### 2. Split conclusion and premise generalization

Apply these operations in order.

#### 2.1 Conclusion-only

For fixed premise `P`, join compatible conclusions:

```text
P -> Q.f1.*
P -> Q.f2.*
    becomes
P -> Q.*
```

Deleting an exact member is allowed only if the representative summary
subsumes it under `BaseOnlySummaryEdgeOps`. Because `P` is unchanged, caller
applicability is unchanged.

This should be the default production operation and should trigger when the
second compatible conclusion arrives.

#### 2.2 Joint premise/conclusion

Only after conclusion canonicalization, optionally join:

```text
P.f1.* -> Q.*
P.f2.* -> Q.*
    becomes
P.* -> Q.*
```

This can make previously inapplicable caller facts applicable. Require:

- relational subsumption of every removed edge;
- the existing static/Value/semantic eligibility restrictions;
- a subscriber-fanout estimate or measured cost guard;
- per-caller deduplication so one representative is not applied alongside
  historical exact members.

### 3. Publish canonical deltas

Storage removal cannot retract facts derived from an earlier publication.

- Canonicalize a single pending add batch before notifying subscribers.
- Coalesce queued, not-yet-processed events by method/partition.
- If a new representative covers exact members still in the queue, publish
  only the representative.
- For already processed exact members, do not attempt invalidation initially;
  prevent their reapplication to new subscribers through current canonical
  storage queries.

### 4. Add a delta-sound BaseOnly subscription index

Index subscriptions by the caller exit access rebased to the callee. For a
summary initial `I` and caller exit `F`, emit only a conservative superset of:

```text
BaseOnlyAccessOps.matchPrefix(F, I)
```

Then retain the existing authoritative delta/exclusion operation. Measure:

```text
candidate amplification =
    subscriptions returned by the index / successful semantic applications
```

This removes rejected broadcast work. It is complementary to summary
generalization.

### 5. Wire the flag only after the implementation is cheap

The production shallow manager currently does not receive the summary-storage
generalization flag. Do not simply enable the current full-rescan
implementation: the corrected Conductor run proves that this reduces facts but
regresses shallow wall time.

First implement incremental conclusion generalization and its tests, then
enable it on `TaintAnalyzer.shallowScan`.

### 6. Keep the fact set unchanged initially

The proposed first mitigation works entirely in summary storage and
subscription routing. It preserves the current fact-set semantics.

This has a hard limit: no summary-only change can reduce the 65,684 steps
inside the synthetic helper itself. After the summary and subscription changes,
measure the remaining top per-method path-edge counts. Only if completed
projects are still dominated by isolated callee-local products should a
separate fact-set abstraction be designed.

### 7. Index initial facts by their current blocker

`BaseOnlyInitialFactAbstraction.registerNewInitialFact` should not scan
`state.added`. For an added access `A`, derive the same short accessor sequence
used by `abstractOneBranch`:

```text
core(A) = static?, field?, value/type-group?, suffix?
```

Under the current exclusion set `E`, define `blocker(A, E)` as the first
accessor in `core(A)` that is not excluded. Abstraction stops there. Growing
`E` can change the abstraction of `A` if and only if the new exclusion delta
excludes that blocker. Earlier accessors were already excluded, later
accessors were unreachable, and a fully traversed fact cannot change.

Keep these writer-owned structures inside each `BaseState`:

```text
blocker accessor -> added facts
concrete-type-blocked fact -> exact type blocker
```

For a concrete type-info blocker, also index it under
`TYPE_INFO_GROUP_ACCESSOR_IDX`, because excluding the group excludes every
concrete type-info accessor. Only these aliased facts need the reverse map;
ordinary facts occupy one blocker bucket without a per-fact map entry.

On an exclusion update:

1. add all new exclusions to `state.excluded`;
2. union and deduplicate the buckets addressed by the raw exclusion delta;
3. remove each candidate's old blocker registrations;
4. run the unchanged abstraction operation only for those candidates;
5. compute and index each candidate's next blocker.

The index is exact under current BaseOnly semantics, not merely conservative.
Every fact moves monotonically through at most four blocker positions, so the
total reprocessing cost is amortized by the size of the stored fact language
rather than `exclusion updates × all added facts`.

An isolated prototype validates the design:

- all 18 focused `BaseOnlyInitialFactAbstractionCasesTest` and
  `BaseOnlyContainsTableTest` cases pass;
- the existing type-group-after-fact case detects and prevents an unsound
  exact-blocker-only implementation;
- with 100 fields × 100 marks (10,000 added facts), excluding one field invokes
  abstraction for 100 indexed candidates instead of scanning all 10,000 facts,
  a 99% reduction.

A matched ThingsBoard experiment confirms that this local lookup was the
blocking cost:

| metric | full-scan abstraction | blocker index |
|---|---:|---:|
| shallow completion | did not complete | 9.210 s |
| final shallow steps | unavailable | 1,404,372 |
| observed heap outcome | grew to 12.87 GiB and cancelled | 10.72 GiB, no high-memory warning |

The indexed run completed before the baseline's +13-second sample. It processed
more work—`pushEntityActionToRuleEngine` finished with 221,881 steps and 51,938
handled summaries, versus 103,008/24,703 in the still-running baseline
sample—and its prescan selected 322 rules rather than 292. Despite that harder
workload, the indexed shallow phase quiesced. At +25 seconds the baseline still
had 14 workers in `NewSideEffectRequirementEvent` /
`registerNewInitialFact`; the indexed phase had already ended.

Do not key this index by the incoming initial fact's access. BaseOnly currently
globalizes requirement exclusions per base; `registerNewInitialFact` ignores
that access. Adding it to the key would be a semantic change and could cause
false negatives. Tree instead keeps access-scoped exclusions in an analyzed
trie and structurally prunes the added access tree; the blocker index is the
flattened BaseOnly analogue.

Required tests:

- randomized differential sequences against the current full-scan reference;
- excluding a later accessor before the current blocker;
- several exclusions in one update;
- exact type-info and type-info-group aliasing;
- facts that have already reached the end of their core;
- static, field, value, and suffix blockers.

### 8. Batch side-effect-requirement growth separately

For one side-effect requirement key, expose the current exclusion union rather
than replaying every intermediate union independently:

1. merge all pending changes for `(method, base, access)` before notifying
   subscribers;
2. enqueue at most one current-state update for that key per processing batch;
3. at the subscriber, process only the exclusion delta since its last observed
   version;
4. do not re-abstract all `state.added` facts once per accessor when several
   exclusions arrive together.

This mitigation is independent of F2F summary generalization and needs its own
differential tests. It can remain on the storage/event boundary; the general
fact-set representation does not need to change.

## Required instrumentation

Keep aggregate counters for:

- accepted path edges by method and statement;
- distinct initials and finals-per-initial;
- exclusion changes and republished finals;
- raw exit candidates, canonical summaries, and published summaries;
- generalization group updates, members, and representatives;
- exact members published before a later representative;
- subscription candidates, successful delta applications, produced sequents,
  and accepted downstream edges;
- side-effect requirement versions, exclusion growth per version, subscriber
  deliveries, and facts re-abstracted per delivery.

The critical measurements are path edges, successful applications, and
downstream accepted edges. Retained summary count alone is not a performance
metric.
