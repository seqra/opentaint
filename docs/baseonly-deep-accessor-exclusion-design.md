# BaseOnly deep accessor exclusion — API analysis and design

Status: **agreed**, and normative for the BaseOnly implementation of this feature.
Written to unblock the rebase of `saloed/base-only-clean` onto `origin/main`.

Where this document and the code disagree, this document is authoritative — with the
one exception that it must itself yield to
[`baseonly-access-domain-spec.md`](baseonly-access-domain-spec.md) §1, whose widening
obligation is what every rule below is derived from.

This document covers the one upstream feature that the BaseOnly access-path mode
cannot absorb mechanically: the deep accessor exclusion introduced by
`a703d61a6` ("feat(core): Implement deep exclusions (#303)").

It is written against `origin/main` at `cbe3b3ffc` (2026-08-20). The local clone
could not reach the remote when this was written, so re-fetch and re-check
[§10](#10-rebase-integration-order) before acting on it.

Normative background this document builds on and does not restate:

- [`baseonly-access-domain-spec.md`](baseonly-access-domain-spec.md) — the BaseOnly
  domain, its packed codec, and the widening obligation in §1.
- [`baseonly-tree-conformance.md`](baseonly-tree-conformance.md) — the five named
  widening rules and the rule that no catch-all approximation waiver exists.

---

## 1. What the upstream feature is

A *starred sanitizer* is a taint-clean rule whose position is `arg.[any]`, or one
carrying the new reach `TaintCleanReach.ExactAndAnyField`. It means: remove this
mark from the argument and from every field below it, at any depth.

Such a rule cannot be evaluated by deleting nodes. The fact being cleaned is
usually *abstract* — it stands for concrete access paths that have not
materialized yet and will only be produced later, when a callee summary delta is
concatenated at the abstraction point. `DeepAccessorExclusion` is the residual
obligation left at that abstraction point: *whatever materializes below me later
must not contain accessor `a`.*

### 1.1 The value

`ap/ifds/access/DeepAccessorExclusion.kt:6-9` — two sorted, disjoint `IntArray`s
of interned accessor indices:

```kotlin
class DeepAccessorExclusion private constructor(
    @JvmField val accessorsFromDepth0: IntArray,
    @JvmField val accessorsFromDepth1: IntArray,
)
```

`null` is the canonical "no claim" (top); `create` returns `null` rather than an
empty object (`:48`).

Writing `Σ` for the accessor alphabet and `γ(N)` for the set of accessor sequences
that may materialize below an abstract node `N`, the denotation is:

```text
γ(N)  =  ε  ∪  (Σ∖D0) · (Σ∖(D0 ∪ D1))*
```

So **`D0` bans an accessor at every position including the one directly below the
node; `D1` bans it at every position strictly below the first.** `D1` members are
tolerated exactly once, as the immediate accessor.

Two buckets are enough, and are needed, for a precise reason. They are needed
because a cleaner at `base.[any]` must *not* remove a mark sitting directly on
`base` — that position belongs to the plain, non-starred clean action
(pinned by `AnyFieldMarkExclusionTest.kt:97-105`). A single flat bucket cannot
express "banned everywhere except position 0". They are enough because the
start-offset domain is closed under the only transformation performed on it: a
claim is created at offset 1 or 0, and each time it is pushed one accessor deeper
`collapseToDepth0()` maps 1 → 0, with 0 a fixed point. Offsets ≥ 2 are
unreachable.

Lattice directions, both exact with respect to that denotation:

| operation | meaning | direction |
|---|---|---|
| `merge` (`:88-99`) | two obligations on the same execution | union of accessors, each at its **strongest** (smallest) depth |
| `intersect` (`:73-86`) | join of alternative executions | only accessors claimed by **both**, at the **weakest** depth |

Using `merge` where `intersect` is required is the one internal way this feature
can produce a false negative: an unsanitized alternative would inherit the
sanitized branch's claim.

### 1.2 The obligation on an access-path mode

The feature adds exactly **one** abstract member, `ap/ifds/access/FactAp.kt:76`:

```kotlin
fun clearAllAccessorOccurrences(accessor: Accessor, keepStartAccessor: Boolean): FinalFactAp?
```

It has exactly **one** engine call site, `taint/Cleaner.kt:225`, inside
`cleanAnyFieldMark`, and the accessor passed is always `cleaner.mark`, a
`TaintMarkAccessor` — never a field. The two call paths are:

| trigger | `keepStartAccessor` | bucket |
|---|---|---|
| cleaner position is exactly `[any]` (`Cleaner.kt:149`) | `true` | `D1` |
| `TaintCleanReach.ExactAndAnyField` on a fact starting with `[any]` (`Cleaner.kt:177`) | `false` | `D0` |

`DeepAccessorExclusion` itself is **mode-private**. Grep confirms it is referenced
only by `AccessTree`, `AccessCactus`, `AccessGraph`, their three serializers, the
shared `DeepExclusionsSerializer`, and two tests. No shared engine code touches
it. A fourth mode may legally never construct one.

`ExactAndAnyField` is not yet produced by any shipped rule: the Semgrep converter
hardcodes `TaintCleanReach.Exact` (`SerializedRuleUtils.kt:53-57`). It is
reachable today only from hand-written rules and the new DSL test suites.

---

## 2. How the existing modes implement it

Worth stating plainly, because the two collapsed modes did **not** reproduce
Tree's discipline, and their shortcuts bound what is expected of a fourth mode.

| | claim granularity | records `D0` | records `D1` |
|---|---|---|---|
| **Tree** | per abstract node, branch-confined | yes | yes |
| **Cactus** | one slot on the root node, used as a per-fact field | **never** | yes |
| **Automata** | one field on the whole `AccessGraph` | **never** | yes, regardless of `keepStartAccessor` |

Only `AccessTree.kt:719` ever calls `addAccessorFromDepth0`. Cactus records
nothing at all on the `keepStartAccessor = false` path
(`AccessCactus.kt:128-132`), so `ExactAndAnyField` degrades there to a pure
structural clean. Both collapsed modes are therefore weaker than Tree by
construction, in the permissive direction.

Two further observations that shape the design below:

- **Where the claim must be honoured is narrow.** Automata split its subsumption
  predicate in two — `containsAll` consults the claim, `containsAllAccessPaths`
  ignores it — and routed *every* analysis-facing call site to the blind version,
  keeping the strict one only in the merge/compression storages
  (`AccessGraphSet`, `AccessGraphStorageWithCompression:89`). Ignoring the claim
  is correct and cheap everywhere except where a fact could be silently swallowed
  by a merge.
- **Being part of fact identity is load-bearing.** It is what stops a cleaned and
  an uncleaned alternative from collapsing into one value in the summary and edge
  storages.

Cactus is not a useful precedent for correctness: it has no end-to-end coverage
for this feature at all, and `AccessCactus.equalTo` / `filterFact` are still
`TODO()`.

---

## 3. Why BaseOnly is the hard case

BaseOnly's abstraction is not a node with children. Per
[`baseonly-access-domain-spec.md`](baseonly-access-domain-spec.md) §3.2 a
canonical access carries **at most one abstraction marker**, and the wildcard is
an *implicit structural self-loop*: `hasVirtualStructuralAny`
(`BaseOnlyAccessOps.kt:522-524`) holds when the field slot is empty and the
terminal is semantic, abstract, or collapsed.

Three consequences:

1. **BaseOnly cannot count depth.** `hasVirtualStructuralAny` makes `!M.$` cover
   `f.!M.$` at every depth, so once the slots are empty there is no representable
   difference between "the mark is immediately below" and "three fields below".
   §4.4 of the domain spec says so directly: `size`/`depth` are a bounded retention
   metric and "must not be used as logical-path lengths". What rescues this is that
   the *occupied* slots still give a sufficient condition for "at least the second
   position", which is what [§4](#4-the-central-decision-d1-is-conditional-not-dropped)
   exploits.

2. **An abstract BaseOnly fact answers "do you contain this mark?" with yes.**
   `headRead` returns `KEEP` for any structural read against a semantic,
   suffix-abstract, or collapsed state (`BaseOnlyAccessOps.kt:472-481`), and
   `startsWith` is `headRead != NONE`. This is deliberate and load-bearing: making
   `startsWith(abstract, mark)` false crashes the engine and costs 17 findings.
   So a BaseOnly fact that keeps a live wildcard after an any-field clean will
   still report the mark as present. **The do-nothing widening cannot honestly
   claim the mark was removed.**

3. **There is no spare bit.** The packed `Long` is exactly saturated:
   16 (static) + 24 (field) + 23 (suffix) + 1 (value-accessor state) = 64. A claim
   must be a side field on `BaseOnlyFinalFactAp`, not a slot.

---

## 4. The central decision: `D1` is conditional, not dropped

BaseOnly cannot *count* depth. But enforcing `D1` does not require counting it —
it requires a **sufficient condition** for "this position is at least the second",
and the occupied slots provide one:

```text
pastFirst(access)  =  staticIdx >= 0  ||  fieldIdx >= 0
```

When `pastFirst` holds, at least one accessor provably precedes the terminal or
the abstraction point, so anything there sits at position ≥ 2 — which `D1` bans.
When it does not hold, the implicit structural Any self-loop may have consumed
zero steps, the position may be 1, and `D1`'s exemption is still live. Enforcing
`D1` there would remove taint BaseOnly cannot prove is gone.

Note `pastFirst` does not need to test static and field separately. When only the
static slot is occupied, `hasVirtualStructuralAny` is still true — it tests
`fieldIdx == NO_ACCESSOR` alone — but the static accessor has itself consumed
position 1, so `≥ 2` still holds.

Three rules follow from the one predicate:

| operation | rule | `pastFirst` of |
|---|---|---|
| clear, concrete mark matches | `keepStart = false` → `null`. `keepStart = true` → `null` iff `pastFirst`, else keep unchanged. | the fact |
| clear, abstract terminal | record the claim at `D0` iff `!keepStart \|\| pastFirst`, else at `D1`. | the fact |
| concat / graft at an abstraction | enforce `D0` always; enforce `D1` iff `pastFirst`. | **the grafted delta** |

**The claim is re-anchored to the abstraction point when it is recorded**, which is
what the second rule does. A `D1` claim therefore survives recording only on a fact
whose abstraction sits at the root, and at graft time the only thing that can
separate the grafted mark from that root is the delta's own occupied slots. So
enforcement inspects **the delta**, not the prefix.

This matches Tree, whose `filterDeepExclusion` applies `D1` accessors to the delta
with `keepStartAccessor = true` — i.e. it removes the mark from the delta at depth
≥ 2 and spares it at depth 1 (`AccessTree.kt:573-575`).

Concretely, grafting into a `base.*` prefix carrying `D1{M}`: a delta `g.!M.$`
yields `base.g.!M.$`, where `M` is at position ≥ 2 and is banned; a delta `!M.$`
yields `base.!M.$`, where `M` may be at position 1, so it is allowed. The second
case over-approximates — the result still denotes `base.f.M.$` via the implicit Any
loop — but that is the widening direction and therefore safe.

A concrete mark that does not match is left alone: marks are terminal-only in the
BaseOnly grammar, so a fact whose semantic terminal is some other mark `N` cannot
contain `M` at any position.

`collapseToDepth0()` is therefore usable, but only across a **provably consumed**
step. `read(f)` on `f.*` returns `TAIL` — one step consumed, collapse is correct.
`read(f)` on `base.*` returns `KEEP` — the self-loop may have consumed nothing, and
collapsing there strengthens the claim into a false negative.

### 4.1 Why the structural half is often exact

The terminal slot is exact, so the `null` results above are not widenings:

- **Terminal is `M`, `keepStart = false`.** Every denoted path ends in `M.$`, so
  every path is banned. Killing the fact loses nothing.
- **Terminal is `M`, `keepStart = true`, `pastFirst`.** `f.!M.$` denotes
  `base.f.(any)*.M.$`, so `M` is always at position ≥ 2. All banned.
- **Terminal is `M`, `keepStart = true`, not `pastFirst`.** The root compact
  semantic terminal denotes both `base.M.$` (which `D1` keeps) and `base.f.M.$`
  (which `D1` kills). BaseOnly cannot split them, so it keeps the fact and retains
  the false positive.

That last row is already the behaviour of the existing `clearAccessor`
(`BaseOnlyAccessOps.kt:199-205`), whose root-semantic-terminal rule keeps the
compact cover for exactly this reason. The new operation extends a rule the mode
already follows.

### 4.2 Consequence: mode 0 and mode 1 differ

`ApMode.BaseOnly` (`fieldSensitive = false`) never installs a field slot —
`prepend` is the identity on structural accessors
(`BaseOnlyAccessOps.kt:176-179`). So `pastFirst` is false for any fact without a
static, and `this.f.!M.$` and `this.!M.$` project to the same value.

Mode 0 therefore lands on the third row above where mode 1 lands on the second,
and must keep a fact that Tree deletes. **This is an inherent field-insensitivity
limit, not a defect** — widening rule 2 of
[`baseonly-tree-conformance.md`](baseonly-tree-conformance.md) §5 applied to a new
operation.

`ApMode.BaseOnlyField`, the production default for the shallow scan, retains the
outermost field and satisfies the second row exactly — but note that satisfying
this row is not enough to pass the cross-mode contract test, for two reasons
unrelated to this feature; see [§8](#8-conformance-and-test-plan).

---

## 5. Design

### 5.1 Representation

Reuse the upstream `DeepAccessorExclusion` rather than introducing a BaseOnly
type. Both buckets carry the same meaning here, and reuse brings `merge`,
`intersect`, `collapseToDepth0`, `contains` and `DeepExclusionsSerializer` with it,
keeping the semantics auditable against Tree.

A single instance per fact suffices — unlike Tree, which needs one per node —
because a canonical BaseOnly access has at most one abstraction marker.

Because the excluded accessor is always a `TaintMarkAccessor` at the only engine
call site, `clearAllAccessorOccurrences` guards with `TODO(...)` on any other
accessor kind. That converts a future upstream widening of the feature into a
crash rather than a silently wrong answer. The enforcement side needs no guard:
it tests membership against the terminal slot, which holds a mark, `FINAL`, or an
abstraction marker.

Four invariants. All are `check`-enforced rather than assumed, because each one is
what licenses a storage to stay on the primitive `Long`, and a silent violation
would drop a claim instead of failing:

```text
I1  claim != null                 =>  the access has an abstraction marker
I2  exclusions is Universe        =>  claim is null            (forExclusions)
I3  initial facts                 =>  no claim, ever
I4  side-effect summary facts     =>  no claim, ever
```

`I1` mirrors Tree's `check(deepAccessorExclusion == null || isAbstract)`. `I2` is
what makes the Z2F and ND storages provably claim-free — see
[§5.4](#54-storage-scope) — so it earns its keep rather than being hygiene. `I3`
keeps `IAP` primitive and also keeps
`MethodNDInitialToFinalBaseOnlyApSummariesStorage:38`'s canonical-access uniqueness
`check` sound, since two initial facts can never differ by claim alone. `I4` is a
stated property of side-effect summaries rather than one derived from the `Edge`
invariants, which is exactly why it is asserted: if it is ever false, the assert
fires loudly instead of the claim vanishing into a `Long`-keyed store.

### 5.2 Per-operation rules

Every operation that rebuilds a `BaseOnlyFinalFactAp` goes through `rewrap`, so each
one needs an explicit decision. This table is the normative list; anything not
listed here leaves the claim untouched.

**Enforcing — the claim changes the result:**

| operation | rule |
|---|---|
| `graftAtAbstraction` / `append` / `appendFinal` | Reject a delta whose terminal is a banned mark: `D0` always, `D1` iff `pastFirst(delta)`. The surviving claim is `merge(prefixClaim, deltaClaim)`, with `prefixClaim` collapsed first iff `pastFirst(delta)`. |
| `covers` (storage subsumption) | Claim-aware: `a` covers `b` only if `a`'s claim is no stronger than `b`'s. See the trap in [§5.4](#54-storage-scope). |
| `mergeAdd` / storage merge | **`intersect`, never `merge`.** A claim-only weakening must still produce a delta rather than being absorbed by an identity fast path. |
| `equals` / `hashCode` | Include the claim. Load-bearing — it is what stops a cleaned and an uncleaned alternative collapsing into one value. |

**Threading — the claim rides along:**

| operation | rule |
|---|---|
| `readAccessor(a)` | Preserve, and `collapseToDepth0()` iff the read provably consumed a step — `headRead` returned `TAIL` or `WRAPPER_TAIL`, not `KEEP`. |
| `prependAccessor(a)` | Preserve unchanged. The claim is anchored at the abstraction point, which does not move relative to the material below it. |
| `rebase(base)` | Preserve. The claim is independent of the base. |
| `abstractOnly()` | Preserve. Tree was changed by this same commit specifically to stop discarding it here (`AccessTree.kt:95`). |
| `filterFact` / type filtering | Preserve. |
| `exclude(a)` / `replaceExclusions(ex)` | Preserve, but drop when the result's exclusions become `Universe` (`I2`). Note this follows Cactus and Automata, **not** Tree, which keeps a claim under `Universe`. |
| `removeAbstraction()` / `restoreAbstraction()` | Preserve across the transient `COLLAPSED` state. Tree nulls here, but BaseOnly's collapse is paired with a restore, so nulling would lose a live claim. |
| `clearAccessor(a)` | Preserve. Unrelated to the deep operation. |

**Blind — the claim is ignored:**

`containsAccess`, `matchPrefix`, `read` as a query, `startsWith`, `delta`, and every
other analysis-facing predicate. This follows Automata, which routes all of these to
its exclusion-blind `containsAllAccessPaths` and keeps the strict predicate only in
the merge and compression storages. Ignoring the claim in a query is a widening.

**Dropped:** a claim does not ride an empty delta in Stage 2 — see
[§9](#9-staged-plan), Stage 3.

### 5.3 Carrying the claim: `FAP` becomes a pair

The shared `FinalApAccess<FAP>.createFinal(base, ap, ex)` has no room for a fourth
component, so the claim travels **inside `FAP`**:

```text
BaseOnlyFinalAp(access: BaseOnlyAccess, deepExclusion: DeepAccessorExclusion?)
```

Storages destructure it: the `Long` goes into the existing fastutil primitive
structures, the claim into a payload beside the `ExclusionSet` one. **No fastutil
storage becomes boxed.**

This is allocation-neutral, not a regression. All nine BaseOnly storages extend
the shared `Common*` generics with `FAP = BaseOnlyAccess = Long`, so every generic
boundary already boxes — and BaseOnly's packed values sit far outside the
`Long.valueOf` cache, so each one allocates today. A purpose-built pair object is
the same single allocation and carries the claim for free. Tree, Cactus and
Automata already use reference FAPs (`AccessNode`, `AccessGraph`), so the shared
layer needs no change at all.

`IAP` stays `BaseOnlyAccess`. The two type parameters are independent, so
`CommonF2FSet<BaseOnlyAccess, BaseOnlyFinalAp>` is well-formed.

One implementation note: `getFinalAccess` is hot. Building the pair on each call
allocates per call rather than per fact. Either hold the pair as the fact's field
and unpack `.access` for the algebra, or cache it lazily on first use — the latter
keeps `BaseOnlyAccessOps` taking raw `Long`.

### 5.4 Storage scope

Only the **F2F family** needs the pair. `Edge.kt:50` and `:137` require
`factAp.exclusions is ExclusionSet.Universe` for `ZeroToFact` and `NDFactToFact`,
while `:89` requires the opposite for `FactToFact`. Combined with the
`forExclusions` invariant in [§5.1](#51-representation), a Z2F or ND final fact
**can never carry a claim**.

| storage | FAP |
|---|---|
| `MethodEdgesInitialToFinalBaseOnlyApSet` | pair |
| `MethodInitialToFinalBaseOnlyApSummariesStorage` | pair |
| `MethodBaseOnlyAccessPathSubscription` | pair |
| `MethodEdgesFinalBaseOnlyApSet`, `MethodFinalBaseOnlyApSummariesStorage` | `Long` |
| `MethodEdgesNDInitialToFinalBaseOnlyApSet`, `MethodNDInitialToFinalBaseOnlyApSummariesStorage` | `Long` |
| `BaseOnlyFinalFactList` | `Long` |
| `FactSESummariesBaseOnlyStorage` | `Long` — side-effect summaries carry no claim (`I4`) |

Two traps in the three converted storages:

**Two merge directions in one place.** In `MethodEdgesInitialToFinalBaseOnlyApSet`
exclusions merge by **union** while the claim must merge by **intersect**.
Reversing either is silent and costs findings.

**`covers` must become claim-aware.** The final-pruning keeps the covering fact.
An unclaimed fact is more general than a claimed one, so pruning the claimed one
is fine — but a claim-blind `covers` also lets a *claimed* fact prune an
*unclaimed* one, dropping taint that should survive. The predicate needs
`a`'s claim ⊑ `b`'s claim, i.e. Automata's strict `containsAll`.

Serialization follows: `BaseOnlySerializer.writeFact` / `readFact` gain the claim
via `DeepExclusionsSerializer` — two length-prefixed arrays of global accessor IDs,
**re-sorted on read**, because every `DeepAccessorExclusion` operation uses
`binarySearch` over per-process interner indices.


## 6. Required API changes

Beyond the deep-exclusion work itself, the rebase forces these. All are shared
engine changes that BaseOnly must follow rather than choose.

**Mandatory to compile:**

1. `FinalFactAp.clearAllAccessorOccurrences(accessor, keepStartAccessor): FinalFactAp?`
   — implement on `BaseOnlyFinalFactAp`. This is the only new abstract member.

2. `MethodSummaryEdgeApplicationUtils` reshape. `SummaryEdgeApplication` is now a
   subtype of a new `EdgeRefinement`, gains an abstract `val delta`, and
   `SummaryExclusionRefinement` becomes `(delta, exclusion)`. Two new deltaless
   cases, `EdgeRefinement.UniverseRefinement` and `IdRefinement`, replace the six
   `SummaryExclusionRefinement(Universe)` call sites in `MethodAnalyzer.kt`. Every
   exhaustive `when` on the BaseOnly summary path needs new branches.

3. `MethodCallSummaryHandler.handleSummary` / `handleZeroToFact` /
   `handleFactToFact` / `handleNDFactToFact` take `EdgeRefinement` instead of
   `SummaryEdgeApplication`. The shared default now concatenates **even on the
   empty-delta path** — so `delta.isEmpty` no longer implies "nothing to apply".

**Shared, no BaseOnly-specific work, but they change behaviour under it:**

4. `Cleaner.kt` is rewritten around a `Cleaner` sealed interface
   (`AllMarks` / `Mark`) and `FinalFactAp.clean(): CleanResult`. The old
   `clearPosition` recursion is gone.
5. `PositionAccess` gains `accessors()` and `hasAnyField()`; `baseIsResult()` is
   removed.
6. `TaintCleanReach` is new; `RemoveMark` and `SerializedTaintCleanAction` gain
   `reach`, defaulting to `Exact`.
7. `ContainsMarkOnAnyField` is a new JVM condition
   (`MethodTaintConfigurationResolver.kt:453`), evaluated by
   `TaintFactAwareConditionEvaluator.evalContainsMarkOnAnyField`. It queries
   `containsAnyPosition` — a read path BaseOnly answers permissively.
8. `AnalysisTest` gains `open val apMode` and `open val analysisUnrollStrategy`.
   This collides with our own ap-mode harness knob; see
   [§10](#10-rebase-integration-order).

**Shared behaviour changes that alter what BaseOnly does, with no signature to fix:**

9. `taint/FactReaderUtils.kt:83` — a previously `error("Impossible")` branch now
   returns `onMismatch(ap, null)`. BaseOnly's collapsed representation can
   plausibly reach it, so a latent crash becomes a live code path.
10. `taint/Source.kt:44-48` — a source precondition whose position ends in
    `AnyAccessor` now retries against the bare base on a miss. This changes which
    BaseOnly facts satisfy a source precondition.

**Stage 2 only, when BaseOnly starts carrying claims** (see [§5.4](#54-storage-scope)):

11. `BaseOnlySerializer.writeFact` / `readFact` gain the claim.
12. `BaseOnlyApAccess.createFinal` applies `forExclusions(ex)`, as
    `CactusFinalApAccess:15` and `AutomataFinalApAccess:10` do. This is what makes
    the Z2F/ND storages provably claim-free.

### 6.1 What actually fails to compile

Exactly **one** production file in the 27-file `baseonly/` package:
`BaseOnlyFinalFactAp.kt`, for the missing abstract member. The other 26 compile
unchanged — no BaseOnly file references `SummaryEdgeApplication`,
`DeepAccessorExclusion`, or any other mode's types, and `common/FinalApAccess`,
`common/InitialApAccess` and `access/util/AccessorInterner.kt` are all unchanged
upstream.

Three files compile but go semantically stale, and are the Stage 2 / Stage 3 work:
`BaseOnlyDelta.kt` (its `BaseOnlyEmptyFinalDelta` stays a `data object` while the
Tree and Cactus equivalents became claim-carrying data classes),
`BaseOnlyFinalFactAp.concat` on an empty delta (still the identity), and
`BaseOnlyApAccess.createFinal`.

Separately, and unrelated to access paths: `d07fe2aed` adds an abstract
`val index: Int` to `CommonInstLocation` (`opentaint-ir-api-common/.../CommonInst.kt:11`)
so `TraceOrdering` can order by `statement.location.index`. **Twelve of our test
files** declare an anonymous `object : CommonInstLocation` and need
`override val index: Int`. Five of them are BaseOnly's own
(`BaseOnlyF2FSummaryStorageLawTest`, `BaseOnlyFactSetTest`,
`BaseOnlySubscriptionAndReqTest`, `BaseOnlySummaryNormalizationTest`,
`BaseOnlyTreeDifferentialStorageTest`). This is mechanical, but **not** a blind
`= 0`: any test with more than one stub statement must give distinct indices or
trace ordering silently degenerates.

---

## 7. Soundness argument

The claim is a filter that only ever *removes* access paths. Dropping it entirely
lands exactly on pre-`a703d61a6` behaviour, where a starred cleaner scrubbed only
the materialized level and the abstraction point re-manufactured the mark. So:

> **Ignoring deep exclusions produces false positives, never false negatives.**

That direction is what makes a staged BaseOnly implementation safe, and it matters
more here than for the other modes: `BaseOnlyField` runs the **shallow scan**,
which selects the rules the full scan will run. A false negative there is a
permanently lost finding; a false positive is only wasted full-scan work.

The design has exactly three places where it could go wrong in the false-negative
direction, all called out above:

1. Collapsing `D1` into `D0` — [§4](#4-the-central-decision-d1-is-conditional-not-dropped).
2. Using `merge` instead of `intersect` at an alternative join — [§5.2](#52-per-operation-rules).
3. Letting a stronger-claimed fact subsume a weaker-claimed one in a storage — [§5.2](#52-per-operation-rules).

Everything else in the design is a weakening and is safe by construction.

---

## 8. Conformance and test plan

`FactCleanerContractTest` is the cross-mode contract, currently enumerating Tree,
Automata and Cactus explicitly (`:39-43`).

**Measured 2026-08-21, and this supersedes the recommendation this section
originally carried.** Enrolling `BaseOnlyApManager(fieldSensitive = true)` was
tried and reverted: **3 of the 5 cases fail**, and none of the three failures is
caused by this feature.

| case | `BaseOnlyField` | cause |
|---|---|---|
| `every representation implements the same cleaner boundary` | **passes** | as predicted below |
| `every representation finds a mark behind AnyField` | **passes** | read path is permissive |
| `plain and any-field cleaners use the same operation` | fails | (B) |
| `any-field keeps its meaning below an exact position` | fails | (B) |
| `exact mark cleanup follows an AnyField abstraction` | fails | (A) |

Two pre-existing behaviours, both orthogonal to deep exclusions and both in the
false-positive direction:

**(A) `clearAccessor` keeps a root semantic terminal.** `BaseOnlyAccessOps.clear`
returns the fact unchanged when the mark is the terminal of a slot-less access,
because the same terminal stays reachable after one or more structural reads. The
failing assertion is the `TaintCleanReach.Exact` half of the test, which requires
`removedAlternative == true`. This is the deliberate rule recorded in the
`clearAccessor` spec, and [§4.1](#41-why-the-structural-half-is-often-exact) row 3
is the same rule applied to the new operation.

**(B) `AnyAccessor` is absorbed on prepend but not matched on read.**
`BaseOnlyAccessOps.prepend` makes `prepend(AnyAccessor)` the identity
(`:167-187`), so `this.[any].!M.$` and `this.!M.$` are the same value — but
`headRead` requires an exact index match against an occupied slot, so
`startsWithAccessor(AnyAccessor)` is **false** for `this.f.!M.$`. The cleaner
therefore never enters its any-field branch and returns the fact untouched. Making
`headRead` treat `AnyAccessor` as consuming any structural accessor would fix
both cases, but it changes a core matching predicate used by source preconditions
and summary matching, so it is out of scope here and recorded in
[§11](#11-open-risks).

Neither failure loses taint: in each the mark is retained where Tree removes it.

**Recommendation:** do **not** enrol either mode in `FactCleanerContractTest`
until (B) is settled. Pin the new operation with a BaseOnly-owned test instead —
`BaseOnlyDeepCleanTest` does this, covering the [§4](#4-the-central-decision-d1-is-conditional-not-dropped)
rules and the mode-0 / mode-1 divergence in both modes.

Additionally:

- `BaseOnlyDeepCleanTest` covers the structural rows of
  [§4.1](#41-why-the-structural-half-is-often-exact) in both modes, including the
  `TODO` guard on a non-mark accessor. **Landed.**
- Run the new `DeepCleanSummaryAnalysisTest` and
  `CleanerFieldSensitivityAnalysisTest` suites under `BaseOnlyField`. Automata
  subclasses both without overriding a single test, which is the bar upstream set.
  Expect BaseOnly to need documented overrides for the depth-2/3 sanitized-field
  cases; each override is a claim about an inherent limit and needs a one-line
  justification.
- Re-run the oracle. Per the branch's history, trace-resolution and recall
  regressions here surface as **dropped findings, not test failures**, and the
  staged pipeline has silent gates that make raw finding counts misleading.
  Never A/B on a single benchmark run.

---

## 9. Staged plan

Each stage is independently shippable and sound; a later stage never invalidates
an earlier one.

**Stage 1 — the operation. LANDED** (rebase of 2026-08-21, folded into the
BaseOnly mode commit because the member is abstract from birth).
`clearAllAccessorOccurrences` with the `pastFirst` rules of
[§4](#4-the-central-decision-d1-is-conditional-not-dropped), the `TODO(...)` guard
on non-mark accessors, and no claim stored. Unblocks the rebase, changes no
storage, adds no bytes. The gap it
leaves is under-cleaning of an abstract-terminal fact, which no shipped rule
triggers today.

**Stage 2 — the claim.** `BaseOnlyFinalAp` as the F2F `FAP`, the construction
invariants, `intersect` on merge, claim-aware `covers`, enforcement in `graft`,
equality participation, and the serializer. Recovers the abstract-terminal case.
Scope is bounded by [§5.4](#54-storage-scope): three storages, not nine.

**Stage 3 — transit through empty deltas.** `BaseOnlyDelta` identity currently
keys on the packed access alone, so a claim cannot ride an empty delta the way
Tree's `EmptyAccessTreeDelta` does. Dropping it there is a weakening, so this is
pure precision recovery. Defer until the DSL suites show it is needed.

**Ordering note.** Stage 2 is not merely an optimisation of Stage 1. Stage 1 alone
leaves the `keepStart = false` / abstract-terminal case silently under-cleaned,
which is the case `TaintCleanReach.ExactAndAnyField` exists to serve. If a rule
using that reach ships, Stage 2 stops being optional.


---

## 10. Rebase integration order

Deep exclusions must be settled **before** the rebase, not during it. Git reports
**zero** conflicts for `a703d61a6` against this branch, because every BaseOnly
file is new and git sees no textual overlap. The breakage is invisible to
`git merge-tree` and to a trial rebase, and it is larger than all ten textual
conflicts combined.

Suggested order:

1. On a scratch branch off `origin/main`, implement Stage 1 and the
   `EdgeRefinement` branches until BaseOnly compiles. Settle it in isolation,
   while it can still be reasoned about separately.
2. Rewrite our branch on the *old* base first: drop `6bedc86b7` (fully subsumed by
   upstream `cbe3b3ffc`) and shrink the four commits that partially duplicate
   upstream `908e924b3`. This roughly halves the conflict surface before any
   rebase begins.
3. Rebase, resolving `MethodAnalyzerEdges.kt`, `AnalysisTest.kt` and
   `Source2SinkTraceGraph.kt` by hand. The last is the hardest commit on the
   branch — upstream *moved* the comparators we edited in place into a new
   `TraceOrdering.kt`, so our edits must be hand-ported to a file that did not
   exist when they were written.

The full commit-by-commit conflict map lives with the rebase work, not here.

---

## 11. Open risks

Things this design does not resolve, recorded so they are not rediscovered late.

**`AnyAccessor` is absorbed on prepend but not matched on read.**
`BaseOnlyAccessOps.prepend` makes `prepend(AnyAccessor)` the identity, so
`this.[any].!M.$` and `this.!M.$` are one value — yet `headRead` requires an exact
index match against an occupied slot, so `startsWithAccessor(AnyAccessor)` is
false for `this.f.!M.$`. Any caller that branches on "does this fact start with
`[any]`" therefore takes the wrong branch, which is what costs BaseOnly two of the
three `FactCleanerContractTest` cases in [§8](#8-conformance-and-test-plan).
Teaching `headRead` to let `AnyAccessor` consume any structural accessor would fix
both, but that predicate is also used by source preconditions and summary
matching, so it needs its own measurement rather than being folded into this
feature.

**BaseOnly's `toString()` becomes load-bearing.** `d07fe2aed` orders traces
deterministically, and `TraceOrdering.TraceFactComparator` falls back to comparing
`InitialFactAp` by `toString()`. If two distinct BaseOnly facts render
identically, trace generation is less deterministic under BaseOnly than under
Tree. Worth a targeted check; it is cheap to test and invisible otherwise.

**Two determinism schemes have not been reconciled.** `d07fe2aed` stabilises trace
ordering; our `9363ce5a8` quotients trace resolution over premises and boundaries,
changing *which* traces exist to be ordered. Getting the merge to compile is not
evidence it is correct, and regressions here show up as dropped findings rather
than test failures.

**`e4df39fd4` rejects `AnyAccessor` on primitives** in `JIRFactTypeChecker`. This
is a real change to fact filtering that BaseOnly has never run against, and it
sits close to the known boxed-primitive mark behaviour. Re-run the mode-0 /
mode-1 comparison after the rebase rather than assuming it is Tree-only.

**`UniverseRefinement` at `MethodAnalyzer.kt:1260`** widens the exclusion set from
`initialFact.exclusions` to `Universe`. That is a behavioural change on a path
BaseOnly's exclusion handling is sensitive to; measure rather than assume.

**Stage 1's under-cleaning is currently unobservable.** No shipped rule emits
`ExactAndAnyField`, so the gap this design deliberately leaves open has no
production consumer to reveal it. That is what makes deferring Stage 2 safe — and
also what makes it easy to forget. The trigger to revisit is the first rule that
sets `reach: ExactAndAnyField`.
