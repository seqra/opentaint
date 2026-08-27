# Read/Write Exclusion Sets

**Status:** draft for review (rev 2)
**Component:** `core/opentaint-dataflow-core/opentaint-dataflow` — `org.opentaint.dataflow.ap.ifds.ExclusionSet`
**Baseline:** census of all 348 `ExclusionSet` references across 92 files at `ee63656f2` on `main`

Splitting `ExclusionSet.Concrete` into two disjoint accessor sets, so that a refinement demand records
*why* it exists. The split is behaviour-neutral by construction: `read ∪ write` is exactly today's set,
and every consumer reads only that.

## Contents

- [§1 What an exclusion means](#1-what-an-exclusion-means)
- [§2 What the split is, and is not](#2-what-the-split-is-and-is-not)
- [§3 The two kinds](#3-the-two-kinds)
- [§4 Merges and their laws](#4-merges-and-their-laws)
- [§5 API](#5-api)
- [§6 Representation, hashing, identity](#6-representation-hashing-identity)
- [§7 Call-site census](#7-call-site-census)
- [§8 Rollout](#8-rollout)
- [§9 Testing](#9-testing)
- [§10 What the labels are for](#10-what-the-labels-are-for)
- [§11 Risks and prior art](#11-risks-and-prior-art)
- [§12 Open questions](#12-open-questions)

---

## 1. What an exclusion means

An `ExclusionSet` annotates the implicit star tail of an *abstract* access path. It says: **this
abstraction point has no information about these accessors, and must be refined before anything can be
concluded about them.**

```
// denotation, verified against AccessNode.filter (AccessTree.kt:646-663)
γ(a.* \ E)  =  { a }  ∪  { a.f.p │ f ∉ E }

// filter() removes immediate children and the isFinal terminal only.
// ExclusionSet is a FLAT, DEPTH-1 constraint. It has no depth structure.
// So x.*\{f} does NOT exclude x.g.f — only x.f…
```

Verified at all four filter implementations, none of which recurses: `AccessTree.kt:646-663` (transforms
only the literal top-level `accessors` array), `AccessCactus.kt:825-839`, `AccessPath.kt:172-176`,
`AccessGraph.kt:959-990` (only edges leaving the initial state). `FinalAccessor` can itself be excluded —
`AccessTree.kt:647`, `val isFinal = this.isFinal && FinalAccessor !in exclusion`. `AnyAccessor` cannot:
`AccessGraphInitialFactAp.kt:32` and `AccessGraphFinalFactAp.kt:26` both open with
`check(accessor !is AnyAccessor)`.

| Value | Meaning | Where it is required |
| --- | --- | --- |
| `Empty` | Maximally abstract — nothing demands refinement. | `AutomataApManager.kt:95`, `TreeInitialFactAbstraction.kt:86` |
| `Concrete(E)` | Abstract, with a refinement demand outstanding on every `f ∈ E`. | Only ever on `FactToFact` edges. |
| `Universe` | No abstract tail at all — the fact is exact, nothing to refine. | `Edge.kt:50` (Z2F), `Edge.kt:133`/`:137` (NDF2F); forbidden on F2F at `Edge.kt:89` |

The demand is discharged by **spawning a separate, more refined initial fact** for the excluded branch —
`TreeInitialFactAbstraction.kt:240-249`, `CactusInitialFactAbstraction.kt:99-124`. That is what makes
adding an accessor to an exclusion set always safe: the coverage given up is picked up by the spawned
sibling. It is also why exclusions are part of fact *identity* (`AccessTree.kt:243-259`,
`AccessCactus.kt:294`, `AccessPathWithCycles.kt:103`) and why `76a3314ba` forces an edge to be
republished when only its exclusion changed.

### Where an accessor first becomes excluded

Exactly **seven** origin sites in the whole engine. Everything else is plumbing, seeding, or
kind-preserving transfer. All seven are unambiguously classifiable, and the classifying information is
already local at each one:

| # | Site | Trigger | Kind |
| --- | --- | --- | --- |
| O1 | `JIRMethodSequentFlowFunction.kt:435` | abstract fact meets a load `x = i.f` | **READ** |
| O2 | `JIRMethodSequentFlowFunction.kt:578` | abstract fact meets a store `i.f = x` | **WRITE** |
| O3 | `GoMethodSequentFlowFunction.kt:240` | `handleComplexRefAssign` — field/index/global read | **READ** |
| O4 | `GoMethodSequentFlowFunction.kt:331` | `complexAccessorWrite` — field/index/global store | **WRITE** |
| O5 | `FactReader.kt:45` | rule condition read a position, missed on an abstract node | **READ** |
| O6 | `MethodSideEffectHandlerWithAnyAccessorRequestHandling.kt:65` | `TaintMarkFieldUnfoldRequest` — any-field mark unfold | **READ** |
| O7 | `CallTypeInfoUtil.kt:34` | `readAccessor(TypeInfoGroupAccessor)` returned null | **READ** |

The JVM discriminator is `sequentFlowAssign` at `JIRMethodSequentFlowFunction.kt:285-300`
(`assignFromAccess is MemoryAccess` → read, `assignToAccess is MemoryAccess` → write); the Go one is the
IR instruction class at `GoMethodSequentFlowFunction.kt:78-93`. In both languages the kind is a
*compile-time constant per entry point* — it never has to be computed, only threaded down a short call
chain that currently erases it.

> **Why this distinction is worth recording.** `MethodFlowFunctionUtils.kt:77-87` defines
> `mayReadAccessor` and `mayRemoveAfterWrite` with **byte-identical bodies**, differing only in name.
> They are the load guard and the store guard, and today they consult the same undifferentiated set. Two
> functions named apart and then written the same is the clearest statement in the codebase that this
> distinction was meant to exist and has not been made yet.

---

## 2. What the split is, and is not

`Concrete` gains a second set. The union of the two *is* today's set, and every operation preserves it
exactly:

```
flat(E)  =  E.read ∪ E.write          // == today's `set`, always

γ(a.* \ E)           depends only on flat(E)
E.contains(accessor) ⟺ accessor ∈ flat(E)
flat(a union b)      =  flat(a) ∪ flat(b)   // today's union
flat(a intersect b)  =  flat(a) ∩ flat(b)   // today's intersect
```

Every existing consumer — the four `filter` implementations, both flow-function guards, the abstraction
registries, the summary-storage subsumption checks — reads `flat` and nothing else. So the split cannot
be observed by any of them. **The change is a labelling change.** The engine keeps doing exactly what it
does today; each refinement demand simply now records whether it arose from a read or a write.

### What this design does not do

- **It does not change what gets excluded.** Merges preserve `flat` exactly (§4). An accessor never
  enters or leaves the set because of its label.
- **It does not change the initial fact.** A write case-split is a case split on the entry fact for
  exactly the same reason a read one is: after `x.f = untainted` the transfer differs by entry fact —
  `arg0.f.* ⊢ ∅` if there was taint under `f`, `arg0.*\{f} ⊢ x.*\{f}` if there was not. Both kinds must
  sit on the initial AP, and `check(initialAp.exclusions == finalAp.exclusions)` (`CommonF2FSet.kt:33`,
  `MethodEdgesInitialToFinalAutomataApSet.kt:77`) stays as it is.
- **It does not implement a consumer.** Nothing reads `read` or `write` separately after this change.
  §10 lists what could, once the labels exist; none of it is designed here.

> **Consequence for review.** Because the split is flat-preserving, it has an exact acceptance criterion
> rather than a judgement call: **tms must produce byte-identical results** (project model at
> `opentaint-test/opentaint-test-tms/opentaint-project/project.yaml`; stock 70 s / 154 findings), and
> `InitialFactAbstractionTest`'s ~60 scenarios must pass unchanged. If either moves, an operation is not
> flat-preserving and the implementation is wrong. That is the whole review question for §§5-8.

The real work, therefore, is not semantic. It is the mechanical surface: two sets where one was, in a
value that is a hash key in every storage in the engine, with an incrementally maintained hash and a
reference-identity fixpoint contract to preserve. §6 is the section that carries risk.

---

## 3. The two kinds

```kotlin
sealed interface ExclusionSet {
    data class Concrete(
        val read:  PersistentSet<Accessor>,   // refine before reading through this accessor
        val write: PersistentSet<Accessor>,   // refine before reading or writing
    )                                         // invariant: read ∩ write = ∅
}
```

| | **READ** | **WRITE** |
| --- | --- | --- |
| Arose from | A load, or a rule condition reading a position that missed on an abstract node. | A store into a field of an abstract fact. |
| Records | "This abstraction point was split because something needed to *read* through `f`." | "…because something *wrote* through `f`." |
| Origins | O1, O3, O5, O6, O7 — five of seven. | O2, O4 — the two store sites. |
| Effect today | Identical. Both close the abstract tail at that accessor and demand a refinement. | ← |

### The kind lattice

`READ ⊑ WRITE`. Read the ordering as demand strength: a write demand subsumes a read demand at the same
accessor, because a point that must be refined before a store must also be refined before a load.
Promotion is upward and is what both merges do (§4).

The choice of `WRITE` as the stronger kind is a convention, not a derivation — nothing today can tell
them apart, so nothing constrains it. It is the convention the requested design specified, it matches the
direction of `DeepAccessorExclusion.merge` ("sequential composition keeps all claims at their strongest
depth", `DeepAccessorExclusionTest.kt:20-28`), and it is the one that makes the disjointness invariant
maintainable with a single subtraction. §10 depends on it; if a consumer there wants the opposite
polarity, this is the decision to revisit.

### Empty and Universe

`Empty` = `(∅, ∅)`, unchanged. `Universe` stays **kind-neutral** — it aligns with anything and returns the
other operand by reference. Giving it a kind ("all accessors as write") would make
`Universe.intersect({a:read})` allocate a promoted `{a:write}` instead of returning `other`, breaking the
reference fast path at `ExclusionSet.kt:30` and `:73` on a hot path. Kind-neutral is also the honest
reading: `Universe` means there is no abstract tail, so there is no demand for a kind to describe.

---

## 4. Merges and their laws

Both merges keep the accessor set they compute today and take the **join in the kind lattice** for any
accessor present in the result. Stated as the requested align-then-combine, and equivalently as a direct
formula:

```
// union — as specified: union both sets, then restore disjointness
write = w₁ ∪ w₂
read  = (r₁ ∪ r₂) \ write

// intersect — as specified: align kinds by promotion, then intersect
w₁' = w₁ ∪ (r₁ ∩ w₂)   ;   r₁' = r₁ \ w₂
w₂' = w₂ ∪ (r₂ ∩ w₁)   ;   r₂' = r₂ \ w₁
write = w₁' ∩ w₂'      ;   read = r₁' ∩ r₂'

// both reduce to the same rule, which is how they should be implemented:
union:      flat = flat₁ ∪ flat₂   ,  write = w₁ ∪ w₂
intersect:  flat = flat₁ ∩ flat₂   ,  write = (w₁ ∪ w₂) ∩ flat
```

|  | `union` | `intersect` |
| --- | --- | --- |
| accessor set | `∪` — unchanged from today | `∩` — unchanged from today |
| kind | promote (`R ⊔ W → W`) | promote (`R ⊔ W → W`) |
| role | merge demands — stronger demand wins | subsume demands |
| callers | 24 | 1 (`MethodInitialToFinalApSummaries.kt:150`, id-edge subsumption) |

### Why union is right at all 24 sites

The exclusion set is a refinement demand, not an assertion of absence, so adding to it is always safe —
the branch given up is covered by the spawned sibling initial fact (§1). That holds for both kinds, which
is why no call site needs to be reclassified and why `union` stays a single operation. It is the same
rationale the author recorded as KDoc on the abandoned `origin/misonijnik/2-star` branch (`f283fd6aa`):

> `join` combines alternative executions: analysis exclusions remain partitioned elsewhere and therefore
> **union**, while a cleaner effect remains true only if every alternative performed it.

Merging two demands on the same accessor then takes the stronger: if one path needed refinement before a
store and the other only before a load, the merged point needs refinement before a store. Promote.

### Laws

| Law | `union` | `intersect` | Note |
| --- | --- | --- | --- |
| commutative | ✓ | ✓ | set ops and kind `⊔` are commutative |
| associative | ✓ | ✓ | `flat` associates as today; kind is a `max` over the operands |
| idempotent | ✓ | ✓ | relies on `read ∩ write = ∅` |
| identity | `Empty` | `Universe` | unchanged; both return the operand by reference |
| absorption | ✗ | ✗ | see below — harmless, but worth stating |

**Absorption fails, and why that is fine here.** With `a = {f:read}` and `b = {f:write}`:
`a.intersect(b) = {f:write}`, so `a.union(a.intersect(b)) = {f:write} ≠ a`. Both operations take the kind
*join*, so neither is the lattice meet, and `(union, intersect)` is a pair of semilattices rather than a
lattice. Today's plain-set version is a distributive lattice, so this is a property genuinely given up.

It costs nothing in practice: nothing in the repository composes `union` and `intersect` on the same
values. `MethodInitialToFinalApSummaries.kt` uses `intersect` at `:150` and `union` at `:271` on two
disjoint sub-storages declared at `:181-182`. And on the `flat` projection — the only thing any consumer
sees — the distributive lattice is intact. Recovering absorption would require one of the merges to
demote, which would mean the two kinds disagree about a shared accessor's demand strength; there is no
reading of §3 in which that is wanted. State the loss in the KDoc and move on.

### Termination

The measure is `(|flat|, |write|)`, increasing lexicographically under `union` and bounded by `Universe`;
`|flat|` decreases under `intersect`, bounded below by `Empty`. Both terminate. The subtlety is not
termination but churn — see §6, "the `===` contract".

---

## 5. API

```kotlin
sealed interface ExclusionSet {
    // --- queries -------------------------------------------------------
    operator fun contains(accessor: Accessor): Boolean   // flat — unchanged behaviour
    fun containsRead(accessor: Accessor): Boolean        // no callers yet; §10
    fun containsWrite(accessor: Accessor): Boolean       // no callers yet; §10
    fun flat(): PersistentSet<Accessor>                  // for the 8 direct .set readers

    // --- growth --------------------------------------------------------
    fun addRead(accessor: Accessor): ExclusionSet
    fun addWrite(accessor: Accessor): ExclusionSet

    // --- merges: names and semantics unchanged -------------------------
    fun union(other: ExclusionSet): ExclusionSet
    fun intersect(other: ExclusionSet): ExclusionSet

    // --- subsumption ---------------------------------------------------
    fun contains(other: ExclusionSet): Boolean

    // --- gone ----------------------------------------------------------
    // add(accessor)     : replaced by addRead / addWrite
    // subtract(accessor): zero callers repo-wide; delete (§12)
}
```

`add` is removed rather than kept as an alias for `addRead`. There are only seven producers (§1); making
each one name its kind is a one-line change per site and is the only mechanism that keeps a future eighth
producer from silently defaulting.

### `contains(other)`

The requested rule is `this.read ⊇ other.read && this.write ⊇ other.write`. It is worth noting that this
is *strictly stronger* than the subsumption order induced by `union`, and differs on exactly one case — an
accessor that is read in `other` and write in `this`, where `this` carries the *stronger* demand and
arguably should still subsume:

```
requested:         a.read   ⊇ b.read    ∧  a.write ⊇ b.write
union-consistent:  a.flat() ⊇ b.flat()  ∧  a.write ⊇ b.write   // ⟺ a.union(b) == a
```

**Low stakes.** `contains(other: ExclusionSet)` has **zero callers** repo-wide and never has had one in
this history — `git log -S "fun contains(other: ExclusionSet)"` shows only the directory-rename commit
`1e96345e1`. Subsumption in the storages uses `union` plus reference identity instead. So either
definition is safe today; the union-consistent one is preferred only because it satisfies the standard
subsumption law and so cannot surprise a future caller. Deleting the method alongside `subtract` is also
on the table (§12).

### Threading the kind to the producers

`FactAp.exclude(accessor)` (`FactAp.kt:29`, `:52`; six implementations) gains a kind. Only three non-test
call sites exist, plus the two JVM `excludeField` aliases at `MethodFlowFunctionUtils.kt:97-99`:

```kotlin
fun InitialFactAp.exclude(a: Accessor, kind: ExclusionKind): InitialFactAp
fun FinalFactAp.exclude(a: Accessor, kind: ExclusionKind): FinalFactAp
```

The kind must reach **both** the initial and the final AP identically at each producer, or
`check(initialAp.exclusions == finalAp.exclusions)` (`CommonF2FSet.kt:33`,
`MethodEdgesInitialToFinalAutomataApSet.kt:77`) starts failing. That assertion holds today only because
the same `ExclusionSet` object is placed on both sides at every construction point —
`GoMethodSequentFlowFunction.kt:469-470`, `JIRMethodSequentFlowFunction.kt:107-108`, `FactReader.kt:56`
vs `:62`, `MethodCallSummaryHandler.kt:127-143`.

**Two short chains to thread:**

| Language | Chain |
| --- | --- |
| JVM | `sequentFlowAssign:285-300` (knows) → `fieldRead:410` / `fieldWrite:472` (constant per branch) → `propagateAbstractFactWithFieldExcluded:591` → the `propagateFactWithAccessorExclude` lambda (`:145`, `:235`, `:342`, `:410`, `:452`, `:472`, `:592`) → sink at `:106-110` |
| Go | `propagate:78-93` (knows) → `handleComplexRefAssign:231` / `complexAccessorWrite:297` (constant) → `PropagationContext:64` → impls at `:456`, `:468`, `:485`, `:505` |

The recursive `fieldRead`/`fieldWrite` calls at `:357`, `:371`, `:427`, `:490`, `:513`, `:565` stay within
one kind, and the forwarding lambdas at `:384-398`, `:505-530` only relay — so the bit is constant per
entry point and needs no analysis.

### Both guards keep reading `flat()`

> **Termination hazard.** The flow-function pattern is
> `if (isAbstract && accessor !in exclusions) { propagateFactWithAccessorExclude(fact, accessor); recurse }`.
> **If the guard queries one set while the producer writes the other, the guard never becomes true and the
> flow function re-emits forever.** This is the tightest coupling in the change and the one thing most
> likely to be got wrong by someone "finishing the split".
>
> `mayReadAccessor` and `mayRemoveAfterWrite` (`MethodFlowFunctionUtils.kt:77-87`) and their Go twins
> (`GoMethodSequentFlowFunction.kt:239`, `:330`) therefore keep reading `flat`. That is also the correct
> semantics: a read-excluded accessor means the point is unrefined at `f`, so a store to `f` equally
> cannot conclude anything. The two functions stop being identical by *producing* different kinds, not by
> querying different sets.

---

## 6. Representation, hashing, identity

This is where the risk in the change actually lives.

### Store `(flat, write)`, expose `(read, write)`

The requested `(read, write)` pair and the internal `(flat, write)` pair are isomorphic —
`read = flat \ write` — and the second is strictly cheaper on the paths that matter:

| Operation | as `(read, write)` | as `(flat, write)` |
| --- | --- | --- |
| `contains(a)` | 2 lookups | **1 lookup — identical to today** |
| `flat()` | set union, allocates | **field read** |
| `union` | 3 set ops + disjointness fixup | `(f₁∪f₂, w₁∪w₂)` — 2 ops |
| `intersect` | alignment pass, then 2 ops | `(f₁∩f₂, (w₁∪w₂)∩f)` — 3 ops |
| `read` | field read | set difference — needed only by `toString` and §10 consumers |

`flat` is the same object shape as today's `set`, so all eight direct `.set` readers keep their exact
current cost, and the alignment pass in the requested `intersect` formula disappears entirely. `write` is
empty at five of the seven origins, and an empty `PersistentHashSet` is a shared singleton.

Make `Concrete` a plain class with a private constructor and a normalising factory rather than a
`data class`. Today's generated `copy()` already leaks a way to build a `Concrete` with a wrong `hash`;
with three fields it would also leak overlapping sets. `DeepAccessorExclusion.create`
(`DeepAccessorExclusion.kt:41-50`) is the in-repo precedent — it enforces its own disjointness by
subtracting depth0 from depth1 and returns `null` for empty.

### Hashing

Today's incremental hash is **correct, not buggy**. `PersistentHashSet` extends
`kotlin.collections.AbstractSet`, whose `hashCode()` is the additive `java.util.Set` contract hash
(verified by bytecode and by execution against kotlinx-collections-immutable 0.3.8). So
`hash + a.hashCode()` in `add`, `hash - a.hashCode()` in `subtract`, and the from-scratch `set.hashCode()`
in `union`/`intersect` all agree — the latter is merely O(n) where it could be O(1).

The two-set hash must stay a pure function of both sets *and* stay incrementally maintainable. A linear
combination distributes over the additive contract:

```
hash          = 31 * flat.hashCode() + write.hashCode()
addRead(a)    = hash + 31 * a.hashCode()
addWrite(a)   = hash + 32 * a.hashCode()      // 31·a (flat) + 1·a (write)
```

> **Do not** use `read.hashCode() + write.hashCode()`. It makes `({f},{})` and `({},{f})` collide —
> precisely the pair the design exists to distinguish — in a value that is a hash-map key throughout every
> storage. And `equals` must compare *both* sets after the hash short-circuit; a single additive hash with
> a one-set comparison makes `({a},{b})` equal `({b},{a})`.

### The `===` contract

Twelve to fourteen sites encode the fixpoint-change protocol as reference identity:

```kotlin
val merged = current.union(added)
if (merged === current) return null   // "nothing new" -> stop propagating
```

This works only because `PersistentHashSet.addAll` returns the receiver when nothing was added (verified
empirically, along with `addAll(self)`, `retainAll(self)`, `remove(absent)`, `add(existing)`). If the new
merges allocate unconditionally, every one of these becomes "always changed" and the IFDS fixpoint stops
converging. The sites: `MethodAnalyzerEdges.kt:192`, `MethodEdgesInitialToFinal{Tree,Cactus,Automata}ApSet.kt`
(`:101`, `:86-90`, `:86`/`:212`), `SideEffectRequirement{Tree,Cactus,Automata}ApStorage.kt` (`:71`, `:75`,
`:114`), `MethodInitialToFinalApSummaries.kt:151`/`:272` (tree) and `:105` (cactus),
`MethodInitialToFinalAutomataApSummariesStorage.kt:137`, `CommonFactSideEffectSummary.kt:97`,
`CommonF2FSet.kt:41`.

```
// invariant each merge must preserve
a.union(b)     === a   ⟺   b.flat ⊆ a.flat  ∧  b.write ⊆ a.write
a.intersect(b) === a   ⟺   a.flat ⊆ b.flat  ∧  a.write ⊆ b.write
```

> **The one place the split is not free.** A **kind-only change** — same `flat`, an accessor promoted
> read → write — produces a new object where today's code returned the receiver. Those detectors then fire
> and re-propagate an edge that carries no new *facts*. Since no consumer reads the labels yet (§2), that
> work is pure waste, and it lands on a branch family already running 7.9× main's event count on
> conductor.
>
> **Gate the change signal on `flat` alone.** Concretely: the merge still stores the promoted label, but
> returns the receiver when `flat` is unchanged, so the "nothing new" path fires exactly as often as
> today. This keeps the behaviour-neutrality claim true of runtime as well as results. When §10's first
> consumer lands, that consumer's design decides whether to flip to the full contract — and it must,
> because by then a label change *is* new information.

### Serialization

The wire format is one byte of kind, then for `CONCRETE` an `int` count and that many `long` accessor ids
(`ExclusionSetSerializer.kt:8-32`). Three AP serializers embed it inline and positionally, with no length
prefix, so any change shifts every following field: `TreeSerializer.kt:26-47`, `CactusSerializer.kt:30-48`,
`AccessGraphApSerializer.kt:25-66`.

**There is no format version field anywhere** in `ap/ifds/serialization/`. The only discriminator on the
persisted blob is `apModeId` (`JIRSummariesFeature.kt:310`, filtered at `:278`), which separates
tree/cactus/automata, not format revisions. A silent format change would mis-decode a stale store rather
than reject it.

In practice the cost is near zero: persistence is gated on `options.storeSummaries`, which defaults to
`false` and is explicitly `false` at every call site found; with it off, `DummySerializationContext` makes
`getIdByAccessor` an `error(...)`. Go has no serialization context at all. Take the cheap defence anyway:
add `ExclusionSetType.CONCRETE_RW = 3` so an old `CONCRETE` blob still decodes, as read-only. The enum is
written as one byte and has three constants, so the fourth is free.

Two read-path notes: `readExclusionSet` rebuilds with `reduce` (`:30`), which throws on size 0 — safe
today only because `Concrete` can never be empty, and *not* safe for a shape where `read` is empty and
`write` is not. And there is currently **no test at all** covering `writeExclusionSet`/`readExclusionSet`.

---

## 7. Call-site census

348 references across 92 files. Only the first group needs a decision; the rest are mechanical or
untouched.

| Group | Count | Action |
| --- | --- | --- |
| **Origins** — an accessor first becomes excluded | 7 | Classify (done, §1). Thread the kind down two short chains (§5). |
| **`exclude()` implementations** | 6 | Mechanical: add a kind parameter and forward it. `AccessTree.kt:54` · `AccessPath.kt:37` · `AccessCactus.kt:53` · `AccessPathWithCycles.kt:23` · `AccessGraphInitialFactAp.kt:33` · `AccessGraphFinalFactAp.kt:27` |
| **Direct `.set` readers** | 8 | Compile break; all want `flat()`. `AccessPath.kt:174` · `AccessTree.kt:196` · `AccessCactus.kt:204` · `AccessGraph.kt:338-339` · `AutomataInitialFactAbstraction.kt:116`, `:125` · `TreeInitialFactAbstraction.kt:55-58` · `ExclusionSetSerializer.kt:12-17` |
| **`union` call sites** | 24 | **No change.** All keep the same operation and the same result set (§4). |
| **`intersect` call sites** | 1 | **No change.** `MethodInitialToFinalApSummaries.kt:150`, id-edge subsumption (added by `745be4bfc`, #241). |
| **Seeding `Empty`/`Universe`** | ~50 | No change. |
| **`replaceExclusions` transfer** | ~25 | No change — copies both sets verbatim. |

The two folds that construct a set from a sequence need their seed accessor named:
`MethodSideEffectHandlerWithAnyAccessorRequestHandling.kt:65` (`fold(Empty, ExclusionSet::add)` →
`::addRead`, per O6) and `ExclusionSetSerializer.kt:30` (`reduce(::union)` — see §6).

### Four pre-existing defects found while surveying

None is caused by this change and none blocks it. Two must be fixed as part of it; two are worth filing.

| Site | Defect | Bearing |
| --- | --- | --- |
| `TreeInitialFactAbstraction.kt:54-63`, `:370` | Flattens `Concrete.set` into an `IntOpenHashSet` and merges with `addAll` instead of an `ExclusionSet` op. The cactus twin (`CactusInitialFactAbstraction.kt:160`, `:177`) keeps a real `ExclusionSet`. | **Must fix** — it would silently drop the labels at that boundary. |
| `MethodEdgesInitialToFinalCactusApSet.kt:86-90` | Returns `null` whenever `mergedAccess === currentAccess`, silently dropping an exclusion-only change. The tree twin at `MethodEdgesInitialToFinalTreeApSet.kt:100-104` propagates it. | **Fix while in here** — one line, and it is on the path §6's identity contract runs through. |
| `AccessGraph.kt:974-979` | The automata representation silently declines to apply a `Concrete` exclusion when the initial state sits on a loop — `"Can't remove accessor because it is in the loop"`. A no-op where tree and cactus filter. Makes `ApMode.Automata` strictly weaker at enforcing exclusions. | File separately. |
| `AccessTree.kt:415-433` vs `:646-663` | `getChild(f)` resolves `f` through an `[any]` child and re-prepends `[any]` when `isCoveredByAny(f)`; `filter` removes only the *literal* `f` branch. So on a tree with an `[any]` branch, `x\{f}` still yields a non-null `getChild(f)`. No compensating logic found. | File separately. Imprecision, not unsoundness. |

---

## 8. Rollout

Three steps, of which only the first two are this change.

### Step 0 — build the oracle, before touching `ExclusionSet`

- Write `ExclusionSetTest`. **None exists today** — nothing pins `add`/`union`/`intersect`/`contains`/
  `equals`/`hashCode`, and in particular nothing pins the `===` identity contract, whose failure mode is
  non-convergence rather than a wrong answer.
- Write the first test of `writeExclusionSet`/`readExclusionSet`.
- Add non-empty-exclusion cases to Go's `SequentRoundTrip` (§9).
- Baseline tms: stock 70 s / 154 findings. Take it in the same window as the comparison run — the box is
  shared, and the same build has measured 103 s and 260-348 s under load.

*Exit:* new tests green against the **current** implementation.

### Step 1 — representation, everything labelled READ

`(flat, write)` internals with `read`/`write` accessors, `flat()` for the eight direct readers,
`addRead`/`addWrite` replacing `add`, `subtract` deleted, the hash and `===` contract of §6,
change-detection gated on `flat`. Every producer calls `addRead`. Fix the two must-fix defects in §7.

*Exit:* tms byte-identical at 154 findings, no wall-clock or heap regression; `InitialFactAbstractionTest`'s
~60 scenarios unchanged. Anything else means an operation is not flat-preserving.

### Step 2 — labelling, O2 and O4 become WRITE

Thread the kind through the two chains in §5. Still flat-preserving, so still behaviour-neutral.

*Exit:* tms byte-identical **again**. Keeping this separate from Step 1 is what isolates the labelling
from the representation: if Step 2 moves a finding while Step 1 did not, the kind is leaking into a
consumer that should not see it.

### Later — consumers, out of scope here

§10 lists the candidates. Each needs its own design, its own flag, and its own A/B; none is a prerequisite
for the others. The first one to land also owns the decision to flip change-detection from `flat` to the
full `===` contract (§6).

Steps 0-2 are worth doing on their own merits even if no consumer is ever built: they add the missing test
coverage, fix two real defects, and make `mayReadAccessor` and `mayRemoveAfterWrite` honestly different.

---

## 9. Testing

| Suite | Role | Change |
| --- | --- | --- |
| `InitialFactAbstractionTest.kt` | ~60 scenarios; the main behavioural contract, run by both the tree and automata subclasses. Exercises the abstraction trie and two of the direct `.set` readers. | Compiles unchanged and **must pass unchanged**. This is the regression oracle for both steps. |
| `ExclusionSetTest.kt` | Does not exist. | **Write it in Step 0.** Pin the `===` contract, the hash/equals invariants, the disjointness invariant, and the two merge laws — including that both preserve `flat`. |
| `SequentRoundTrip.kt` (Go) | Drives `GoMethodSequentFlowFunction` — producers O3/O4 and both guards. | **Blind spot.** Its `final(exclusions: ExclusionSet = ExclusionSet.Empty)` default means it never constructs a non-empty exclusion, so the termination hazard in §5 has no test. Add cases in Step 0. |
| `DeepCleanSummaryAnalysisTest.kt`, `CleanerFieldSensitivityAnalysisTest.kt` | End-to-end canaries. The former already contains a probe for exclusion smearing at joins. | No change; watch them. |
| `FactCleanerContractTest.kt` | Cross-representation cleaner contract over all three AP managers. | Compiles unchanged; cheap smoke coverage. |
| `DeepAccessorExclusionTest.kt` | Different type. Read it for the naming convention the new merge tests should follow. | None. |

> **Sample-suite blind spot.** Every passthrough regression sample — `PassthroughFileModelSamples`,
> `PassthroughSerializationSamples`, `PassthroughContainerSamples`, `PassthroughValueFlowSamples`,
> `PassthroughServletAccessorSamples`, and the `java.io.File` accessors at `rules/test/rule-test.yaml:483-499`
> — puts source, library call and sink inside a **single entry-point method**. That is precisely the
> configuration in which an exclusion never crosses a summary boundary. 677 passing rule-tests with 0 false
> negatives would prove nothing about this area. Any new sample here needs a cross-method variant.

All three AP modes need coverage. `ApMode.Tree` is the default (`CommonAnalysisOptions.kt:20`,
`AbstractAnalyzerRunner.kt:32`); `Automata` is pinned by `CleanerFieldSensitivityAnalysisTest` and
`DeepCleanSummaryAnalysisTest`; `Cactus` has the weakest coverage and one of the §7 defects.

---

## 10. What the labels are for

None of this is designed here, and none of it is required to justify §§5-8. It is the list of things that
become *possible* once a demand records its origin, so that the split is not built blind.

| Candidate | Sketch | Where it would land |
| --- | --- | --- |
| **Filter exclusions at the summary boundary** | The one `todo` in this area: the caller's whole exclusion set is stamped onto the summary's result fact after concatenating a non-empty delta — i.e. after the tail those demands were computed against has moved. Filtering needs to know which demands are still meaningful at the new tail; the label is one axis of that provenance. | `MethodCallSummaryHandler.kt:118-124` |
| **Narrow the wholesale resets** | Three places blank the exclusion set entirely because they cannot tell demands apart. With labels, a reset could keep the demands still relevant to the channel it is resetting for. | `MethodAnalyzer.kt:274` · `MethodCallFlowFunction.kt:131`, `:208` |
| **Kind-aware requirement emission** | Go emits a `Sequent.SideEffectRequirement` on every exclusion; the JVM sink does not. If read and write demands need different requirement shapes, that asymmetry becomes expressible instead of accidental. | `GoMethodSequentFlowFunction.kt:472` vs `JIRMethodSequentFlowFunction.kt:106-110` |
| **Make the two guards genuinely different** | The motivating observation (§1). Any change here must respect the termination hazard in §5 — the guard that gates re-emission has to keep seeing the whole set. | `MethodFlowFunctionUtils.kt:77-87` |

Two of these — the `todo` and the resets — are the sites where the engine visibly gives up on provenance
today. They are the best evidence that a provenance axis is wanted, even though neither is a reproduced
defect.

---

## 11. Risks and prior art

### A similar shape was tried and abandoned

> **Read before implementing.** The abandoned commits `87f89cf0d` / `8ae13478b`, "Handle deep exclusion in
> exclusion set", put a second kind **inside `Concrete`** — two `PersistentSet`s plus a
> `mergeAndIntersectDeep`, with `union` asserting `check(deepExclusion.isEmpty())`. That shape was
> abandoned for a separate type, which landed on main as `DeepAccessorExclusion` (`a703d61a6`, #303).
>
> **It is not the same situation.** That attempt tried to house a genuinely different mechanism: a
> *depth-unbounded, destructive* sanitisation claim, which does not merge like a refinement demand — hence
> the assertion, which is the author noticing that one `union` could not serve both. The read/write split
> houses two instances of the *same* mechanism with the *same* denotation, which is why both merges keep
> working unchanged (§4). Still: that history is the reason to hold the flat-preservation property as a
> hard invariant rather than a convenience. The moment a kind stops merging like a demand, it belongs in
> its own type.

The wider prior art is the `origin/misonijnik/2-star` branch, which split this domain once along *demand
vs cleaner-effect*: `f283fd6aa` → `3526e2b72` (`FactDemandState`) → `0cec5d1e1` → `4050182da`. Its
`FactFlowState` KDoc is the only written specification of these merge semantics anywhere in the history.

### Do not re-absorb cleaner effects

`DeepAccessorExclusion` is deliberately separate, with the depth structure `ExclusionSet` lacks
(`accessorsFromDepth0`/`accessorsFromDepth1`), living on tree nodes rather than on the fact, forbidden on
initial APs (`AccessGraphInitialFactAp.kt:17-19`), and merging by *intersection* on alternatives because a
sanitisation claim survives only if every path made it. The two mechanisms touch at exactly one point:
`ExclusionSet.Universe` kills the deep annotation, because a fact with no tail can never have a delta
concatenated (`DeepAccessorExclusion.kt:106-107`, `AccessGraph.kt:104-105`, `AccessTree.kt:104`,
`AccessCactus.kt:321-324`, `AccessGraphFinalFactAp.kt:57-59`). Keep it that way.

### Memory

Every `Concrete` gains a field, and `a.*\{f:read}` and `a.*\{f:write}` become distinct hash keys where they
were one — so edge duplication is possible in every storage keyed by fact identity, including the
per-instruction `arrayOfNulls<ExclusionSet>` arrays at `MethodAnalyzerEdges.kt:175` and the three
`MethodEdgesInitialToFinal*ApSet` classes. There is **no interner for `ExclusionSet`** (only for
`Accessor`, `AccessNode` and `AccessPath`), so nothing absorbs the extra allocation.

Against that: `write` is empty at five of the seven origins and an empty `PersistentHashSet` is a shared
singleton, and gating change-detection on `flat` (§6) keeps the duplication from turning into propagation.
The net is small but should be measured, not assumed. Use conductor at **16 G**, scored by
events-before-the-memory-guard — at CI's 8 G every build in this family saturates, so the comparable
quantity is how much work completes, not whether it finishes. Run-to-run noise on that metric is under 1%.

### Smaller notes

- **Pseudo-accessors.** Only `FieldAccessor` and `ElementAccessor` are real heap accessors
  (`AnyAccessor.containsAccessor`). `TaintMarkAccessor`, `FinalAccessor`, `ValueAccessor`,
  `TypeInfoGroupAccessor` and `TypeInfoAccessor` can never carry a write demand; O7's
  `TypeInfoGroupAccessor` is READ for this reason. Worth an assertion in `addWrite`.
- **`ValueAccessor` and `TypeInfoGroupAccessor` are plain `object`, not `data object`**
  (`Accessors.kt:159`, `:172`), so their hash codes are identity-based and vary per JVM run. Irrelevant to
  persistence — only accessor *ids* are serialized — but an `ExclusionSet` hash can never itself be
  persisted.
- **`ExclusionSet.kt` has no KDoc at all.** The definitions in §1 and §3, and the flat-preservation
  invariant, should land on the type as part of Step 1. The only written specification of these semantics
  currently lives on an abandoned branch.

---

## 12. Open questions

1. **Delete `contains(other)` and `subtract`?** Both have zero callers repo-wide. Keeping dead API through
   a change that makes its semantics subtler invites a future caller to pick the wrong one. If they stay,
   `contains(other)` should get the union-consistent definition (§5) and `subtract` should split into
   `subtractRead`/`subtractWrite` — a single `subtract` removing from both is the only shape that cannot be
   expressed as a composition, and nothing asks for it.
2. **Is the disjointness invariant worth enforcing, or just maintaining?** A normalising factory makes it
   unrepresentable. A `check` makes violations loud. Given the type is allocated on the hottest path in the
   engine, the factory alone is probably right, with the `check` behind an assertions flag.
3. **One exclusion set, many abstraction points.** A tree- or cactus-form fact can have several abstract
   nodes at different depths but carries a single `ExclusionSet` (`AccessTree.kt:47-49`), and
   `AccessPath.splitDelta` (`:151-161`) applies it at whichever abstract node the walk bottoms out at —
   while the flow functions only ever exercise the root (`GoMethodSequentFlowFunction.kt:239` tests
   `currentFact.isAbstract()`, which is root-only). Pre-existing, unresolved, and not made worse by the
   split — but if the per-edge reading is not the intended one, both kinds are mis-scoped and §10's
   consumers would inherit that.
4. **Does the abstraction memo need doubling?** `TreeInitialFactAbstraction.registerNewInitialFact` and
   `AutomataInitialFactAbstraction.registerNew` track "which accessors have already been case-split" as a
   flat `BitSet`. Flat is correct for this change by construction. A §10 consumer that makes a read demand
   and a write demand into different obligations would have to revisit it.

---

*Census taken at `ee63656f2` on `main`; line numbers are from that commit. Claims about
`PersistentHashSet` hash and identity behaviour were verified against kotlinx-collections-immutable 0.3.8
by bytecode inspection and execution.*

*Revision 2 withdraws two claims from revision 1 — that `union` needs a demoting variant at join sites, and
that write exclusions do not belong on the initial fact. Both were wrong: the exclusion set is a refinement
demand rather than an assertion of absence, so union is safe for both kinds, and a store on an abstract
fact is a case split on the entry fact for the same reason a load is.*
