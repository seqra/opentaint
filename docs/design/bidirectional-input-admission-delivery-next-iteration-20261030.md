# Next iteration: remove redundant caller-input state and work

Date: 30 October 2026. Base analyzer:
`edb2e06cdb17eecafbe03415236bf56c57910239`.
Status: proposal only. No change below is implemented.

Use the [current measurements](../reports/bidirectional-identity-owner-protection-performance-20261030.md).
Latest reached / complete / accepted iterations are OWASP **run-5 / run-5 /
run-5**, conductor **run-4 / run-3 / run-3**, thingsboard **run-2 / run-1 /
run-1**, and Stirling-PDF **run-6 / run-5 / run-5**.

The previous three optimizations are implemented. Their old hotspot estimates
are not the current workload. Static owner search is largely removed. Compact
point storage works. Large caller-input directories and generic input admission
remain. Conductor also has a measured regression which needs separate tracking.

## 1. Priority and semantic scope

| Priority | Proposed change | Current evidence | Work or storage to avoid |
|---|---|---|---|
| 1 | Store literal static subscription families with exact full-mark membership | 7.99 million eligible rows form 465,029 families; subscription managers retain about 3.07 GB | Per-mark input wrappers and repeated candidate entries for the same route/geometry |
| 2 | Do not rebuild no-op generic input merges; use the exact delta mask | Stirling run-6: generic caller admission dominates mask work | Mask union and tree construction with no result; two proved redundant mask intersections for fresh results |
| 3 | Link only fresh restricted-run subscription input | At least 2.42 million conductor run-4 and 1.31 million Stirling run-6 offers were not fresh | Duplicate callee entry work and repeated coordinates in cumulative offers |
| 4 | Share matching for static writers with one complete premise | Thingsboard run-1 binding takes 232.465 seconds | Repeated candidate scan and match for different conclusions of the same writer premise |

Priority is a design order across different workloads. It is not a common
speedup prediction. Priority 1 has an exhaustive current heap eligibility
census. It does not yet have a measured byte-saving estimate. This census
checks the subscription entries directly, not the point-store identity count.

**No analyzer semantic change is proposed.** Keep the same fields, tails,
exclusions, full marks, layers, protection, rules, aliases, ND premises,
source/sink observations and stop policy. Keep each complete MethodKey and
caller route. Run-1 remains FULL by default. This is not a return to mark-group
abstraction. Every full mark stays distinguishable.

The modified mechanisms are storage layout, necessary candidate selection,
generic admission construction, and restricted-run input delivery. They are
not permission to skip a rule, weaken a field update, merge caller premises,
invent an input or change the demand emitter. Keep semantic equality and
hashing unchanged. No GroundingSupport, new edge flag, WeakIdentityCache,
SoftReferenceManager rewrite or IR storage change is part of this proposal.

The proof and adapter gates below must pass before runtime changes. If a
counterexample requires a semantic change, present its code and facts for a
decision. Do not hide that change inside a storage helper.

## 2. Literal static subscription families

### 2.1 Current storage and proposed storage

`SubscriptionManager.byCallee` owns caller-side input directories.
`AddedFactAccumulator` stores one key and entry for each exact
`(CallerRef, GroupKey)`. Its candidate trie stores input handles. A full mark
is part of CallerRef's original initial. Thus many equal routes and literal
static images can create one complete group per mark.

Proposed first scope:

```text
restricted run, FULL marks
one nonzero InitialAp with named static field base/path
one exact canonical initial image of the same full mark
empty protection mask
same exact header/layers as the current input
```

Use the current literal-image recognizer as the starting contract. Exclude
ZERO, ND, root/class markers, multiple paths/marks, protected images and
unsupported headers in the first implementation. They use the current
accumulator. Keep nonempty E when valid; do not replace it with Empty.

```kotlin
// Storage-only shape. It is never used as an abstract semantic premise.
data class StaticInputFamilyKey(
    val callee: MethodKey,
    val caller: MethodKey,
    val originalShape: InitialShape, // complete path, tail and E; concrete-slot role
    val callerLayer: Layer,
    val call: CommonInst,
    val stageOrdinal: Int,
    val inputHeader: ExactInputHeader,
)
class StaticInputFamily {
    val members: MutableFullMarkSet // exact IDs T,U,...; no wildcard group token
}
```

Remove only the full-mark value from the physical family key. Store that
value in exact membership. Keep the callee, full caller MethodKey, call,
stage, caller layer, link layer, path, tail and exclusions. A family is owned
by the same caller runner/directory as the old rows. It is not a global cache.

```text
decode(family, T):
  original = originalShape with concrete full mark T
  ref = CallerRef(caller, original, callerLayer, call, stage)
  added = exact canonical image of original at input layer
  return Subscription(callee, ref, input layer, added)
```

Use the direct typed initial-image constructor for decoding. Do not rebuild
through a generic Facts normalizer which can change a tail or layer. Here
"exact canonical image" means literal equality with that constructor; it does
not mean Tail.EXACT. The measured large families include Tail.ANY.

An unsupported update promotes only that T to the old representation. Restore
its exact old image without a fresh replay or an extra interner admission,
then apply the offered update with the old admission function. Keep other
marks in the family. A changed GroupKey remains a separate group, as now.
A protection-only upgrade must promote and propagate; ordinary Facts equality
must not hide it. Keep fallback permanent for that route/group.

Preserve the existing managed interner's logical admission cadence in the first
implementation. A compact family must not silently skip the tiny admissions
which affect later interning. The current input Fact already exists: retaining
the existing interner call while discarding an unneeded stored header is an
acceptable first adapter. Promotion restoration must not count it twice.
Apply this requirement to first admission, later updates and promotion, not
just counter decrements. A long literal root can be interned and returned as
canonical storage. Preserve that stored sharing or use the legacy path for
that case. A source-bound reconstruction test must check both paths.

### 2.2 Avoid candidate products

For a concrete FULL premise T, an eligible family can select T directly from
membership. It still uses the existing complete AP predicate before callback.
A FLOW or unsupported group premise uses the required members and the old
predicate; it must retain mark-exclusion and group/full compatibility rules.
No caller route or ND member is merged.

```kotlin
val selected = geometricCandidates(publication, member).flatMap { posting ->
    when (posting) {
        is LegacyInput -> captureCurrentSnapshot(posting)
        is StaticInputFamily -> {
            val marks = exactFullSelectorOrFallback(publication, member, posting)
            captureDecodedSnapshots(posting, marks)
        }
    }
}
// Capture ALL candidates before ANY callback can grow another family.
for (snapshot in selected) visit(snapshot)
```

Preserve the old candidate/callback order in the first adapter. Exact mark
membership order alone is not necessarily the old posting order. Keep compact
logical order metadata without restoring per-mark key/entry wrappers. If a
later design changes that order, prove callback permutation equivalence first;
equal final AP denotation alone is insufficient. Keep deferred and inline
replay policy unchanged.

The input trie stores a family posting once instead of one posting per mark.
For k full marks at one otherwise identical route/geometry, k concrete
publications can need k qualifying family members instead of a k-by-k mark
candidate product. FLOW publications can still require all k routes. Do not
claim that their AP grafts or call continuations are automatically batched.
Any later bulk FLOW application needs a separate equivalence proof and scope.

### 2.3 Example

```java
void helper() { /* no direct access to C.f */ }
void relay() {
    helper(); // call S
}
```

Consider two legal incoming run-2 relations at S:

```text
I_T = (S.C.f.*, T); actual = (S.C.f.*, T), DEMAND
I_U = (S.C.f.*, U); actual = (S.C.f.*, U), DEMAND
same caller, callee, call S, stage and caller layer

Current: two input keys, entries, Facts headers and candidate handles.
New: one exact static family; members={T,U}.

Publication with concrete T premise:
  select T; construct the same original I_T and actual T input.
  Do not deliver it through the U route.

FLOW publication:
  keep all compatible members; apply the same complete predicate and callbacks.

Later actual S.C.g/T for the old T route/group:
  promote T, restore its old C.f/T image, then admit C.g/T as before.
  U remains compact. No restored value is replayed as fresh.
```

This is a storage/admission example, not a claim that the short helper body
alone creates every marked input.

### 2.4 Current census and proof gates

At the thingsboard run-2 guard snapshot, the source-bound query visits all
10,818,019 input entries in 83,326 directories. It finds:

```text
eligible literal static concrete identities: 7,990,412
exact-scope markless route families:            465,029
unchanged fallback entries:                  2,827,607
potential total physical rows:               3,292,636

eligible marks / family: mean 17.18, maximum 20
families with 18 exact marks: 388,620
duplicate eligible mark memberships: 0
```

Keeping fallback unchanged gives **3.286-fold row-count potential**. This is
not a proved byte or engine speedup: mark membership, family headers and
promotion storage still cost memory. It identifies the repeated exact-full-mark
dimension inside the 2.062 GB retained input accumulator set. The 3.073 GB
subscription-manager set includes that set; do not add them.

The query uses conservative physical caller/call IDs within each exact
directory. Runtime family keys must keep current MethodKey/CallerRef semantic
equality. Do not substitute object identity to match the measurement helper.
The census excludes ZERO, nonstatic, root/class, FLOW, and nonidentity entries.
It validates literal images and masks; it does not infer their safety from
overlapping AP denotations. The complete histogram and top family records
are in the report's embedded data.

Prove decoder equality for full current input state, fresh deltas, index
candidate support and each complete callback route. Prove one-way promotion,
mask upgrades and whole-candidate snapshot-before-callback behavior. Use generated event
sequences and the current AddedFactAccumulator as a reference. Test all tails,
E, layers, repeated marks, two contexts, two calls, two stages, cross-mark
updates, ND/ZERO fallback and deferred replay.

Measure exact eligible logical groups, physical families, mark multiplicity,
promotions, index postings, candidate tests and retained bytes. Count logical
input groups separately from physical family containers. Do not replace one
per-mark directory with another per-mark object map. Keep all unsupported rows
in the old path. This eligibility census supports selection; the source
adapter and differential proof gates still control implementation.

## 3. Skip no-op generic construction and use exact mask differences

Current `ApManager.mergeAddDelta` builds merged protection and normalizes a
stored tree before AddedFactAccumulator rejects a null delta. Fresh merges
also intersect the merged mask with the delta tree. This is the remaining
large Stirling path; it is distinct from the TaintGroup optimization already
implemented.

```kotlin
check(old.groupKey == offered.groupKey)
val (root, ordinaryDelta) = taintAlg.mergeAddDelta(old.root, offered.root, cancellation)
val annotationDelta = difference(offered.nonSubsumable, old.nonSubsumable)
if (ordinaryDelta == null && annotationDelta == null) return old to null

val mask = union(old.nonSubsumable, offered.nonSubsumable)
val deltaRoot = union(ordinaryDelta, annotationDelta)!!
return includedMergeTree(old, root, mask) to
    includedMergeTree(old, deltaRoot, annotationDelta)
```

The private constructor uses exactly the existing base, layer, E and tail
canonicalization. General factories, restrictions, `withRoot`, `withProtection`
and arbitrary-mask operations keep their trims. Do not reuse the merged mask
as the delta mask. Do not reject an annotation-only update.

For exact coordinates, with P0⊆R0 and P1⊆R1:

```text
D = R1 \ R0                   dP = P1 \ P0
Q = D ∪ dP                    P = P0 ∪ P1
P ⊆ R0 ∪ R1                  P ∩ Q = dP ⊆ Q
```

An old protected coordinate cannot be in D or dP. An offered protected
coordinate in D must be in dP. The delta therefore needs exactly the already
computed annotationDelta. If D and dP are empty, state and header remain old;
no new tree or mask union is needed.

```java
// copyAsT/AsU assign T/U to the output when the input has T.
Box build(Box p) {
    Box x = new Box();
    copyAsT(p.left, x.left);
    copyAsU(p.right, x.right);
    return x;
}
```

A representative admission trace is:

```text
old R={left/T}, P={left/T}
offer R={left/T,right/U}, P={left/T}

Both versions: stored R={left/T,right/U}, P={left/T}; delta R={right/U}, P={}.
Current: intersect merged P with both stored and delta roots.
New: use included stored P and dP={}; perform neither intersection.

Repeated identical offer:
Both: no fresh delta. New: return before merged-mask/tree construction.

New protection on an old right/U coordinate:
Both: emit right/U with protection. It is not a no-op.
```

The facts illustrate the merge kernel; source/cleaner rules can supply the
protected and unprotected inputs. They are not all inferred from this one
method body.

Stirling run-6 spends 75.47% of Java samples in mask intersection and 75.00%
in caller-input accumulation. The focused leaf sample attributes 8,060 of
8,351 mask leaf samples to the generic merge route. These are overlapping
scopes, not percentages to add. Removing the full-root walks is a large target;
the data do not give a guaranteed whole-project speedup.

The [checked constructive model](../../spec/lean/proposals/input-admission-next-20261030/README.md)
has 28 named theorems and 55 audited declarations. It proves annotated state
and delta equality, no-op return, exact delta-mask difference and a finite
leafwise emission kernel. The Kotlin adapter and complete analyzer are not
verified by this model. Before implementation, bind exact trie delta/minus
semantics and canonical headers to those proofs.

## 4. Send only fresh restricted input to the callee

Current code admits/replays a subscription and then sends the original input
even if admission rejected it:

```kotlin
subscribe(offered)
link(callee, ref, offered.layer, offered)
```

Return the existing admitted delta through the port:

```kotlin
val fresh: Facts? = subscribe(offeredSubscription) // same registration and replay
if (config.run1) link(callee, ref, offered.layer, offered)
else if (fresh != null) link(callee, ref, fresh.layer, fresh)
```

Keep subscription registration, replay, exact CallerRef, ND support and
required send handling. Keep the normal ZERO-origin/nonzero-Fact path distinct
from zeroOnly/Reach control. The explicit backward ZeroIn path stays unchanged.
No new input cache, barrier or callee standing added-fact store is needed.

For one route, old input `{left/T}` followed by `{left/T,right/U}` already
replays only `{right/U}`. The new code also links only that fresh payload.
An identical later offer creates no link.

| Incomplete engine | Received input offers | Fresh normal + control subscriptions | Conservative nonfresh offer bound |
|---|---:|---:|---:|
| conductor run-4 | 4,856,738 | 2,439,370 | 2,417,368 |
| thingsboard run-2 | 16,262,677 | 16,088,539 | 174,138 |
| Stirling run-6 | 2,334,947 | 1,029,061 | 1,305,886 |

Every normal link follows a subscription attempt. Fresh normal offers are no
more than all fresh subscriptions, including controls. Cancellation can leave
fresh offers undelivered. Thus received offers minus all fresh subscriptions
is a conservative lower bound, not a count of individual AP coordinates.
This gate alone has little support as the main thingsboard fix.

The source adapter must prove that limit plus C2 emission distributes over
**literal coordinate union** for fixed demand and policy. Never use semantic
AP coverage to compact inputs: an exact child below an ANY parent can supply
new refinement. Test that cell, annotation-only changes, canonical delta
headers, field/mark exclusions, all tails, static completion in run-2 and
inline/deferred replay. If distributivity fails, retain whole offers for that
case; do not change the emitter to make the optimization pass.

## 5. Share run-1 writer matching

Thingsboard's writer phase considers 222,569,600 inputs for 2,351,008 writers.
Matching uses the complete owner and initial I, not the writer conclusion C.
Group pending conclusions by `(full owner MethodKey, complete I)`:

```kotlin
for ((ownerAndInitial, writers) in detachWriterGroups()) {
    visitCurrentInputs(ownerAndInitial) { input ->
        val matched = matchInput(ownerAndInitial, input) ?: return@visitCurrentInputs
        for (writer in writers) applyExistingWriter(writer, matched, input)
    }
}
```

Keep each distinct writer effect, actual qualified input and onBound callback.
Keep the existing recursive agenda: a later writer in the same group still
needs its own conclusions applied to current inputs. Do not retain a global
I-by-input match cache.

For `set(p){ C.a=p; C.b=p; C.c=p; }`, consider two inputs with the same
actual/original facts but different call or stage refs. The current input key
keeps both. Three writers match them six times. One shared writer batch
matches twice and still applies all six qualified effects. Fully equal input
keys are already deduplicated; they are not another source of savings here.

A separate joined-only input projection could match once and apply three
effects only after proving that call/stage fields are unused by every guide
callback. This additional reduction is not established by writer grouping.
Live caller subscriptions always keep those fields.

For k_g writers, n_g candidate inputs and b_g late blocks:

```text
old matching: Σ k_g*n_g
new matching: Σ b_g*n_g
all required full writer/input effects remain
```

Current shared-premise and site-free multiplicities are not measured. Writer
work is 223.083 seconds; binding is 232.465. A twofold binding reduction needs
more than half of binding work to disappear. Even deleting the entire writer
phase cannot halve thingsboard's 620.915 engine-plus-binding seconds. This is
useful transition work, not a claim to meet the 60-second run-1 engine target.

## 6. Do not select unsupported shortcuts

- Within-delivery coalescing has only about 0.062% raw surplus in the current
  thingsboard snapshot. Actor pending publications have about 1.72% surplus.
  Do not sell this as a twofold fix. Conductor's different batches need their
  own multiplicity evidence before this becomes a selected target.
- Queued LinkIn has 28.54-fold potential header-lane packing, but queues retain
  only about 114 MB. Repeated payloads in the same exact callee/layer/header/
  root/mask scope are few. This is not a global duplicate-object count.
  Literal field/mark union,
  initial-emission and counted-work fairness proofs are required; a semantic
  ConclusionGroup compaction can lose refinable children. Keep this as a
  separate scheduling study, not an unproved duplicate filter.
- Generic field-based call skipping is not supported by current footprints.
  Rules, cleaners, aliases, models and returns can affect a static even when
  the method body does not name it. DEMAND aliases must not be dropped.
- A run-3-or-later callee with no nonzero demand has only ZERO-origin new
  inference, but immutable native/reversed records can still be required.
  A no-record fast path needs exact candidate checks and measured hit rate.
  Whole-offer one-shot replay is not yet a replacement for fresh replay.
- FLOW SCC routing is a study. Query-specific owners and typed endpoints must
  remain exact. A memo for operand pairs does not remove duplicate results
  produced by different pairs.
- The interner cadence difference is proved by source. Its contribution to
  conductor's regression remains unproved. Track it separately; do not rewrite
  cache ownership or reference management silently.

## 7. Implementation and measurement gates

1. Use the completed priority-1 eligibility census as the baseline. Model its
   decoder and promotion before changing the directory. Measure actual bytes
   and candidate counts after the change; do not convert row ratios to bytes.
2. Add differential tests against current input accumulation, complete AP
   matching, fresh deltas and callback routes. Preserve mask-only updates and
   full MethodKey/call/stage/layer separation.
3. Implement no-op/exact-mask admission and fresh restricted links as atomic
   changes after their source adapters pass. Preserve all run-1 behavior.
4. Implement compact families only in the proved scope; keep unsupported
   rows and public semantic equality unchanged. Keep interner cadence explicit.
5. Add writer matching only after its grouping and callback proof passes.
6. Run complete core/JVM suites and formal checks. Then repeat the authorized
   16 GB/FULL/aliases/statics/`1,1,2,...` campaign. Reuse the legacy report.

Compare exact completed observations and frontiers where available, not just
counts. Record latest reached, complete and accepted run labels. Report input
admission calls, logical groups versus physical families, selected candidates,
mask work, allocations, actual retained bytes, peak pending work and every
incomplete endpoint. A faster OOM is not convergence. A representation saving
at a larger frontier is not a fixed-work memory-saving measurement.
