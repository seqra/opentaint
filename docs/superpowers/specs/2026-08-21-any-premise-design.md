# `[any]` as a first-class premise accessor

Bounding the initial-fact-abstraction explosion caused by `[any]` unrolling.

- **Branch**: `saloed/13-any-premise-design`, from `saloed/5-default-get` @ `4c358d2e1`.
- **Status**: design. A working prototype of an earlier, less clean variant exists on
  `saloed/12-any-unroll-budget` (`a6e5be532`); its measurements are quoted throughout as evidence.
- **Scope**: the tree access-path backend (`ApMode.Tree`, the default). The cactus and automata
  backends are out of scope.

---

## 1. Problem

A `$*VAR` whole-object source rule seeds a fact of the shape `arg0.[any]![mark].$` — "the whole
object at `arg0`, at any depth, is tainted". `[any]` denotes **zero or more** field or element steps:

```kotlin
// ap/ifds/Accessors.kt:145 -- which accessor kinds [any] ranges over
fun containsAccessor(accessor: Accessor): Boolean = accessor is FieldAccessor || accessor is ElementAccessor
```

The *zero*-or-more reading is settled (§3.5): it is what `getChild`, `contains` and
`AccessTreeAnySuffixMatcher` implement, and what `FactCleanerContractTest:110-121` pins across all
three backends.

`[any]` and `.*` are **not** interchangeable, and it is worth being explicit about why, because the
notation invites the confusion. Read `.*` as an **existential** — "there is taint at or below here,
we have not resolved where" — and `[any]` as a **universal** — "every suffix below here is tainted",
which is exactly what a `$*VAR` whole-object source asserts. So `X.[any].*` and `X.*` are different
facts, and the difference survives concatenation: `X.[any].b.*` and `X.b.*` are genuinely distinct.

A summary **premise** (`InitialFactAp`, concretely `AccessPath`) cannot express `[any]` — the
representation silently drops it:

```kotlin
// access/tree/AccessPath.kt:296
accessor == ANY_ACCESSOR_IDX -> this // todo: All accessors are not supported in tree base ap
```

So `TreeInitialFactAbstraction` cannot key a summary on such a fact directly. Instead it **unrolls**:
for every accessor the analysed trie has seen at that level it materialises a concrete fact
`arg0.a.[any].*`, `arg0.b.[any].*`, …, then repeats one level deeper. The premise set this produces
is the product of the exclusion sets along every path.

Measured on conductor (`-Xmx8g`, IFDS timeout 600 s):

| | baseline |
|---|---:|
| F2F premises emitted (`abstract.facts.emitted`) | 891,654 |
| `[any]` branch descents | 22,278,704 |
| premise-match tests | 5,320,752 |
| methods emitting >1024 premises | 36 |
| methods emitting >16384 premises | 5 |
| worst single method | 305,222 premises |

The worst method is `WorkflowExecutorOps#rerunWF`, and a provenance trace attributes its premises to
a single root: the Spring dispatcher entry point for `WorkflowResource#rerun`, whose
`RerunWorkflowRequest` argument carries a `$*UNTRUSTED` mark and is unpacked into five separate
arguments one call later. Conductor does not converge at 8 GB — it OOMs
(`rc=253`, `AbstractAnalyzerRunner.exitProcessIfNotOk`).

**Goal**: bound the enumeration without losing any flow.

---

## 2. How it works today

All citations are against `access/tree/TreeInitialFactAbstraction.kt` (**TIFA**) at `4c358d2e1`.

### 2.1 State

One `TreeInitialFactAbstraction` per `NormalMethodAnalyzer` (`MethodAnalyzer.kt:173`), partitioned by
access-path base (`this`, `arg0`, `ClassStatic`, …) — state never crosses bases. Per base
(`MethodSameBaseInitialFact`, TIFA:290-329):

| field | meaning |
|---|---|
| `added` | the union of every concrete fact that has arrived at this entry point for this base, merged into one access tree. Monotone. |
| `analyzed` | an `AccessPathTrieNode` trie of the premises already handed out, plus the exclusion sets they accumulated. |

`AccessPathTrieNode` (TIFA:331-380) has three fields, and the tri-state of `terminals` — exposed as
`exclusions()` — is load-bearing:

- `null` — no premise ever ended at this prefix. The walk stops here and **emits the prefix as a premise**.
- non-null but empty — analysed, nothing excluded yet. The walk descends but emits nothing.
- non-empty — analysed, and these accessors were explicitly excluded. They are exactly the refinement
  demands, and they are also the `[any]` unroll candidates.

`unrolled` is a persistent per-node memo of which accessors have already been materialised out of an
`[any]`. `AccessPathTrieNode.unrollAccessors` both reads and commits in one pass (TIFA:347-354), so
it is **one-shot**: an accessor never produces a second unroll request at the same node. That is the
round loop's termination guarantee.

Crucially, **`[any]` can never be a trie key**, because `AccessPath.AccessNode.addParent` drops it
(`AccessPath.kt:296`). The blockage is structural, not policy.

### 2.2 The pair the abstraction emits

`addAbstractedInitialFact(fact)` returns `List<Pair<InitialFactAp, FinalFactAp>>`, consumed by
`MethodAnalyzer.addInitialEdge` (`MethodAnalyzer.kt:550-553`) as
`FactToFact(entryPoint, P, entryPoint.statement, F)`: **`P` is the key the summary is stored under,
`F` is the fact the body is analysed with from the entry statement.**

Both components fold the *same* accessor sequence (TIFA:85-92), so the pair is the **identity**
`(P, P.*)`:

```
P = arg0.a.b.c            createNodeFromReversedAp        (AccessPath.kt:351)
F = arg0.a.b.c.*          createAbstractNodeFromReversedAp (AccessTree.kt:1822)
```

The contract test pins it: `initial == expected && final.equalTo(expected)`
(`InitialFactAbstractionTest.kt:98-101`). Each emitted premise is registered into the trie with an
*empty* exclusion set in the same callback (TIFA:91), so it is never emitted twice.

### 2.3 The round loop

One round = one worklist walk of the current fact against the `analyzed` trie
(`abstractAccessPath`), emitting premises and *collecting* — not executing — `[any]` unroll requests;
then `unrollAnyAccessors` materialises them and returns the delta they add to `added`, which becomes
the next round's input (TIFA:72-98). The split exists because `abstractAccessPath` is `inline` and
must not mutate `added` while walking it.

For a request `(prefix R, node N, accessors A)` and each surviving `a ∈ A`, the new fact is
`base.R.a.N'` — **the entire fact subtree that carried the `[any]`, re-rooted one accessor deeper**.
`N` still contains its `[any]` child, so `arg0.[any].*` becomes `arg0.a.[any].*`: the `[any]`
survives one level down, and the next round repeats. Four filters can reject a candidate: the
`AnyAccessorUnrollStrategy`, the `FactTypeChecker` accessor filter, a whole-subtree re-filter, and
`addParentIfPossible` structural legality (TIFA:100-141).

### 2.4 How a summary is applied

At a call site, for caller fact `F_caller` and premise `P`:

1. `AccessTree.delta(P)` walks `P`'s accessor chain through `F_caller` using **`getChild`**, returning
   the residual subtree `d` (`AccessTree.kt:178-210`).
2. `d` is grafted onto the summary's conclusion at every `isAbstract` node —
   `concatToLeafAbstractNodes`, whose graft test is literally `if (isAbstract && other != null)`.

Two consequences the design depends on:

- The `*` that `F` plants at `P`'s endpoint survives into the conclusion and **becomes the graft
  point**. A premise whose endpoint node is not `isAbstract` has no graft point, and every delta
  against it is silently discarded.
- A caller fact activates **every** premise that is a prefix of it, not only the most specific one
  (`AccessBasedStorage.collectNodesContains` adds the current node at every level).

### 2.5 Where deeper premises come from

Demand-driven, not enumerated. When a flow function meets a field it cannot see through under an
abstract premise, it refines: `propagateFactWithAccessorExclude` calls `initialFactAp.excludeField`
(`JIRMethodSequentFlowFunction.kt:106-110`), `MethodAnalyzer.handleInputFactChange` notices the
premise changed (`MethodAnalyzer.kt:618-628`), and `registerNewInitialFact` folds the accessor into
that trie node's `terminals`. The next walk then finds `exclusions.contains(accessor)` and emits
`prefix.accessor` where it previously stopped at `prefix` (TIFA:245-250).

This is also the amplifier: growing an exclusion set re-arms `unrollAccessors` at that node, so every
newly demanded accessor becomes an unroll candidate, and `registerNewInitialFact` re-walks the entire
monotonically growing `added` union rather than a delta (TIFA:68 vs TIFA:39-42). The type filter does
not contain it — `accessPathFilter(emptyList())` returns `AlwaysAcceptFilter`
(`JIRFactTypeChecker.kt:184`), so depth-0 unrolling is unfiltered, and deeper it is only a
permissive `typeMayHaveSubtypeOf` test on the last accessor.

### 2.6 What the unrolling actually buys

**Unrolling is the precision feature.** It converts `arg0.[any]![mark].$` into concrete paths like
`arg0.MapValue.externalInputPayloadStoragePath![mark].$`, and the resulting premise states *exactly
which field sequence must be tainted* for the summary to conclude its final fact. A caller matching
that premise is known to have taint at precisely that path.

The representation constraint — a premise cannot hold `[any]` — is why unrolling is the *only*
available mechanism today, but it is not the reason the mechanism is valuable. Removing it is a
deliberate trade of **precision for performance**, and this design should be read as such rather than
as a pure win.

### 2.7 Prior art in the other backends

- `CactusInitialFactAbstraction` has no `[any]` handling at all — input facts are stripped by
  `withoutAnyFieldAccessorExclusions()` — so it has neither the capability nor the explosion. It does
  show that a premise with a **non-empty** exclusion set is legal to emit
  (`CactusInitialFactAbstraction.kt:59-65`).
- `AutomataInitialFactAbstraction` **already does something close to what this design proposes**: it
  handles `[any]` without a round loop and without a persistent `unrolled` memo, emitting in a single
  pass one premise per (analysed graph × excluded accessor) whose delta *starts with the any-accessor
  index* — `analyzedGraph.concat(prepend(accessor))`,
  `AutomataInitialFactAbstraction.kt:193-236`. Deeper levels happen only when a later
  `registerNewInitialFact` grows that graph's exclusion set. That is the automata-backend spelling of
  "`[any]` belongs in the premise", and it is evidence the shape is workable.

## 3. Design

### 3.1 Core: let a premise hold `[any]`

Make `ANY_ACCESSOR_IDX` a first-class accessor inside `AccessPath`, instead of being dropped by
`addParent`. Then the frontier needs no special case at all — the abstraction walk descends the
`[any]` edge like any other accessor and emits the ordinary identity pair:

```
P = arg0.a.b.[any]
F = arg0.a.b.[any].*
```

This is the shape proposed in review, and it is strictly cleaner than keying the frontier on the
plain prefix `arg0.a.b`:

- **`arg0.a.b` is too weak.** Every caller fact at or below `a.b` matches it, because all prefix
  premises fire. The summary built for the `[any]` frontier would then be applied to concrete facts
  that have nothing to do with it — pure over-approximation, and measurably expensive.
- **`arg0.a.b.[any]` is exactly right.** It is a strong precondition: the only facts with a
  non-empty delta against it are facts that themselves carry `[any]` at `a.b`.

#### The invariant this abuses

A premise holding `[any]` is a very strong precondition — structurally, only a caller fact that
*itself* carries `[any]` at that position can match it. Ordinarily that would be reckless. It is safe
here because of what triggered the premise in the first place:

> The `[any]` premise is only ever emitted while abstracting a fact that carries `[any]` at that
> position, and that fact is in this entry point's `added` set. So a fact strong enough to match the
> premise is **known to exist**; the premise can never be vacuous.

Two things follow, and both must be kept in view:

- **No flow is lost.** The `[any]` premise is emitted *in addition to* the premises the ordinary walk
  produces. A caller sending a concrete fact `arg0.a.b.c.*` still matches the concrete premises
  produced for it by the normal demand-driven mechanism (§2.5); it simply does not match the `[any]`
  premise, which is correct, because that premise exists to serve the `[any]`-carrying fact.
- **Precision is what is traded.** Under unrolling the premise named the exact field sequence
  required. Under `[any]` it names "some sequence of covered steps". The conclusion is correspondingly
  coarser. That is the cost of the feature and it is deliberate.

**The matching property already holds under the existing `delta`/`getChild` implementation** — no
change to the matching logic is required. Tracing `getChild(ANY_ACCESSOR_IDX)` (`AccessTree.kt:415-433`):

```kotlin
val node = getNodeByAccessor(accessor)                       // the [any] subtree, or null
val anyAccessorNode = getNodeByAccessor(ANY_ACCESSOR_IDX)
    ?: return node                                           // no [any] in the fact -> null -> empty delta
val anyChild = anyAccessorNode.getNodeByAccessor(accessor)   // nested [any], normally null
var resultNode = mergeAddMaybeNull(anyChild, node)
if (manager.isCoveredByAny(accessor)) { ... }                // false for ANY: not a Field/Element
return resultNode                                            // the [any] subtree
```

`isCoveredByAny` delegates to the production `AnyAccessorUnrollStrategy`, which returns true only for
`ElementAccessor` and `FieldAccessor` and explicitly false for `AnyAccessor` — so the re-prepend
branch does not fire and `getChild(ANY)` is a plain "does this fact carry `[any]` here" test that
returns the subtree below it.

### 3.2 Marks fall out for free

Because the walk treats `[any]` as an ordinary accessor, a frontier fact `arg0.[any]![mark].$`
produces a premise that continues *past* the `[any]`:

```
P = arg0.[any]![mark]
F = arg0.[any]![mark].$ …
```

`[any]` covers field and element steps only, so a taint mark, a class static, type info, and the
`[final]`/`$` terminator are **not** reachable through it. Under a design where premises cannot hold
`[any]`, that forces an explicit split of the frontier into "accessors `[any]` covers" (one coarse
edge) and "accessors it does not" (one edge each, accessor concrete on both sides) — which is what
the prototype on `saloed/12-any-unroll-budget` implements. **Allowing `[any]` in the premise makes
that split unnecessary**: the ordinary walk produces both kinds of premise uniformly.

This matters, and is the reason the naive version of this feature fails. Measured: collapsing the
frontier onto a bare `.*` (or `[any].*`) loses conductor's findings **2 -> 0**, and the two lost
rules are `java/security/ssrf.yaml:ssrf` and `java/security/path-traversal.yaml:path-traversal` —
precisely the rules whose marks the provenance trace attributed to the starred Spring sources.

### 3.3 The cap

Unrolling now becomes optional — a *precision* dial rather than a correctness requirement.

- Count, per `(method entry point, access-path base)`, how many concrete facts have been materialised
  out of `[any]`.
- Below the limit, unroll as today: concrete premises are more precise.
- At the limit, stop unrolling that base and let the walk emit the `[any]` premise instead.

The cut is sticky per base, so the premise set a base contributes is bounded. Because
`AccessPathTrieNode.unrollAccessors` is one-shot, an accessor the analysis demands *later* still gets
its own premise: the cap bounds the enumeration, it does not close the frontier.

At limit 100 on conductor exactly three bases are cut, and they are the methods the provenance trace
named: `WorkflowServiceImpl#rerunWorkflow`, `WorkflowExecutorOps#rerun`, `WorkflowExecutorOps#rerunWF`.

### 3.4 The concat optimisation: `[any]` consumes the covered delta prefix

When a delta `d` is grafted onto an abstract leaf sitting **directly below an `[any]` edge**, the part
of `d` that `[any]` already denotes is redundant. Consume the longest prefix of `d` made only of
accessors `[any]` covers, up to the first one it does not:

```
[any].*  ⊕  x.y.z.![mark].$   ->   [any].![mark].$      (not [any].x.y.z.![mark].$)
[any].*  ⊕  x.y.z.*           ->   [any].*              (fully covered: absorbed)
[any].*  ⊕  ![mark].$         ->   [any].![mark].$      (nothing to consume)
[any].*  ⊕  x.[any].![m].$    ->   [any].![m].$         (nested [any] also consumed — see C3)
```

**Sound, under either reading of `[any]` (§1).**

- *Existential reading* (`[any].S` denotes the path set `{ w·p : w ∈ Covered*, p ∈ ⟦S⟧ }`): for any
  path `w·x·y·z·![m]·…` with `x,y,z,w ∈ Covered`, `w·x·y·z ∈ Covered`, so the path is already in
  `⟦[any].![m]⟧`. The absorbed fact is a superset.
- *Universal reading* (`[any].S` asserts `S` holds after **every** covered suffix): instantiating the
  quantifier at `w := w'·x·y·z` shows `[any].![m]` implies `[any].x.y.z.![m]`. The absorbed fact is
  the stronger assertion, so it marks taint on more paths.

Either way absorption moves in the safe direction — a monotone coarsening, path-wise. No taint can be
lost, on any branch, for any prefix length.

**Why it matters.** `concatToLeafAbstractNodes` applies its no-repeated-field normalisation only via
`accessor.isFieldAccessor()` (`AccessTree.kt:1291`), and `ANY_ACCESSOR_IDX` has basic kind
`TYPES_OR_MARKER_KIND`, so the engine's only structural depth bound is not enforced below an `[any]`
edge. Absorption removes the field steps from below `[any]` altogether, which is a *stronger* bound
than the one being bypassed. Measured with `[any]` kept symbolic in facts:

| | baseline | capped | capped + absorption |
|---|---:|---:|---:|
| mean fact tree size | 43.1 | 289.4 | 222.5 |
| mean fact depth | 7.6 | **47.0** | **5.8** |
| facts >1000 nodes | 5 | 22,867 | 17,331 |
| progress | 2,372,147 | 293,185 | **875,586** |
| live heap | 7377 M | — | 5255 M |

The measured column is an *unsound* ablation that drops the graft entirely (it fails C1 below), taken
only to size the prize: **3.0x throughput**.

**It is not really optional.** Without it the feature is correct but slower than baseline (§7 R1).

#### Five constraints, all mandatory

- **C0 — absorb *before* the two limiters, and make them O(1).** The graft chain today is
  `filterTypes -> limitElementAccess -> filterDeepExclusion`, and the descent additionally calls
  `other?.limitFieldAccess(accessor, …)` per field accessor of the conclusion. Both limiters exist to
  bound structure that `[any]` is about to absorb anyway. Running absorption first leaves a residual
  whose head is, by construction, the first accessor `[any]` does **not** cover — so
  `limitElementAccess` finds no leading element chain and `limitFieldAccess` finds no occurrence of
  the field to strip. Both degenerate to O(1) no-ops and do real work only when an uncovered accessor
  is actually present. Given how hot this path is — `concatToLeafAbstractNodes` grafts at *every*
  abstract node of the conclusion — this is plausibly a larger win than the size reduction itself.
- **C1 — hoist `isAbstract`/`isFinal` from the collapsed leaf.** Every delta leaf is abstract or final
  (`isEmpty = !isAbstract && !isFinal && accessors == null`). If a fully-covered branch is
  implemented as "nothing to graft", then `:1314` rebuilds the node with `isAbstract = false`,
  `concatNode` is null so the abstraction is never restored, and `takeIf { !it.isEmpty }` at `:1319`
  **drops the whole branch — lost taint.** That is exactly what the ablation above does. `mergeAdd`
  already unions the flags and intersects `deepAccessorExclusion`, which is the join wanted; hoisting
  must route through it or `manager.create`, never a raw `AccessNode` constructor (the init asserts
  `deepAccessorExclusion == null || isAbstract`).
- **C2 — the deep-exclusion claim must be evaluated at the *original* depths.**
  `DeepAccessorExclusion` is **depth-relative** (`accessorsFromDepth0` vs `accessorsFromDepth1`).
  Absorption changes the relative depth of everything it hoists, so hoisting a `![m]` from depth 4 to
  depth 0 turns it into a *start* accessor, and a depth-1 claim that would have deleted it now keeps
  it — silently defeating the sanitizer.

  This is in direct tension with C0. The resolution is not to reorder but to **carry the absorbed
  depth**. `filterDeepExclusion` already distinguishes the two cases by a `keepStartAccessor` flag:

  ```kotlin
  deepAccessorExclusion.accessorsFromDepth0.forEach {
      filtered = filtered.clearAllAccessorOccurrences(it, keepStartAccessor = false, …)
  }
  deepAccessorExclusion.accessorsFromDepth1.forEach {
      filtered = filtered.clearAllAccessorOccurrences(it, keepStartAccessor = true, …)
  }
  ```

  If absorption consumed at least one step, every surviving accessor is logically at depth >= 1, so
  **both** sets apply — i.e. the depth-1 set must also be applied with `keepStartAccessor = false`.
  Threading a single "absorbed anything" boolean into `filterDeepExclusion` satisfies C0 and C2
  together, and is strictly *more* aggressive filtering than today (more precise, sound direction).
  If absorption consumed nothing, behaviour is unchanged.
- **C3 — a nested `[any]` must also be consumable.** `isCoveredByAny(ANY_ACCESSOR_IDX)` is **false**,
  so a literal reading of "up to the first accessor `[any]` does not cover" *stops at a nested
  `[any]`* and still produces `[any].[any]…` — the shape `AccessTreeAnySuffixMatcher` aborts the run
  on. The predicate must be `acc == ANY_ACCESSOR_IDX || manager.isCoveredByAny(acc)`. This is sound
  (`[any].[any]` denotes a subset of `[any]`) and means **this optimisation resolves §5.2 rather than
  merely coexisting with it.**
- **C4 — guard on the immediate parent edge being `[any]`.** Consuming into a path like `[any].f.*` is
  **unsound**: `[any].f.x.![m]` and `[any].f.![m]` are disjoint. A stronger variant lifting the
  residual across intervening covered edges up to the `[any]` ancestor is also sound but needs a
  pending-lift list threaded up the recursion; take the local form first.

Use **`TreeApManager.isCoveredByAny`** (the injected `AnyAccessorUnrollStrategy`), not
`AnyAccessor.containsAccessor`. The whole tree backend uses the strategy as the operative denotation
of `[any]`, and in tests the strategy is deliberately narrower — using `containsAccessor` would be
unsound there.

#### It also restores an invariant the read path already assumes

`getChild` for a covered accessor `a` on a node with child `[any] -> A` returns
`A.getChild(a) ∪ [any].(A \ a) ∪ direct(a)`, whereas the exact residual of `⟦[any].A⟧` after consuming
`a` is `⟦A.child(a)⟧ ∪ ⟦[any].A⟧`. These agree **iff `A` has no covered accessor at its top level** —
i.e. iff the normal form this optimisation establishes already holds. Where it does not hold,
`getChild` is *already* lossy. So absorption is not merely a size optimisation: it establishes the
normal form the read path is written against.

### 3.5 `[any]` is zero-or-more — settled

The docstrings say "one or more", but the implementation is *zero* or more, and that is the reading
this design adopts. Three sites are only correct under it:

- `getChild`'s `anyChild = anyAccessorNode.getNodeByAccessor(accessor)` term (`AccessTree.kt:423`) —
  reads `a` from `N.[any].a` as if the `[any]` consumed nothing;
- `contains`'s `if (anyAccessorNode.contains(accessor)) return true` (`:400`);
- `AccessTreeAnySuffixMatcher`'s root trie node, seeded with `suffixNode.isFinal` at depth 0, so that
  `[any].$` trims a bare `$` out of a merge peer.

And `FactCleanerContractTest:110-121` pins it across tree, automata and cactus: `base.[any].![m]`
must answer a read of `base.![m]`.

It bears repeating that this is about the *number of steps* `[any]` spans, not about `[any]` versus
`.*`. Those two remain distinct quantifiers (§1): `.*` is existential, `[any]` is universal, and
`X.[any].*` is a strictly stronger assertion than `X.*`. The selectivity of an `[any]` premise
(§3.1) is therefore real and not merely representational — it genuinely admits only facts carrying
whole-subtree taint at that position.

Consequences used elsewhere in this document:

- `[any].<covered sequence>.[any]` ≡ `[any]`, which is what makes the nested-`[any]` collapse of §5.2
  a normalisation rather than an approximation.
- The absorption of §3.4 is a coarsening under either the existential or the universal reading — see
  the soundness argument there.
- The docstrings say "one or more" and should be corrected as part of the work.

## 4. Soundness

The obligation is the summary-application contract. For a returned pair `(P, F)` the body is analysed
once from `F`, the summary `P -> E` is recorded, and for every caller fact `c ∈ γ(P)` the engine emits
`E.concat(c.delta(P))`. Therefore:

- **(S1) `F.contains(P)` must hold** — the node at `P`'s endpoint in `F` must be `isAbstract`, because
  that is the graft point `concatToLeafAbstractNodes` requires. The identity pair
  `(arg0.a.b.[any], arg0.a.b.[any].*)` satisfies this: `getChild(ANY)` lands on the abstract node
  below the `[any]` edge.
- **(S2) `F` must be no finer than what `P` admits** — anything under `P` that `F` omits is a fact a
  caller genuinely has that the summary claims to cover. Identity satisfies this by construction.
- **(S3) Coarsening `F` is FN-safe** — a larger entry state yields a superset of derivations. It costs
  precision (possible false positives), not recall.

The cap only ever *replaces* an enumeration of concrete premises with one `[any]` premise that
denotes their union, and every accessor `[any]` cannot express continues to get its own premise via
the ordinary walk. No flow is dropped.

Empirical check on the prototype, with the cap forced to its most aggressive setting
(`anyUnrollLimit=1` — cut after the very first unroll):

| suite | result |
|---|---|
| `:opentaint-dataflow-core:opentaint-jvm-dataflow:test` | **98 passed, 0 failed** |
| `:opentaint-java-querylang:test` (rule-level, asserts expected findings) | **237 passed, 0 failed** |

---

## 5. Two representation invariants that must change

Both must change or the feature is silently inert or crashes. Both were hit in the prototype.

### 5.1 The `maxDepth` inflation: 10_000 -> 10

`AccessTree.AccessNode` adds a sentinel to `maxDepth` for any node carrying an `[any]` child
(`AccessTree.kt:307-309`):

```kotlin
if (containsAnyAccessor()) {
    depth += 10_000
}
```

`MethodAnalyzer.edgeExceedLimit` compares `factAp.depth` against a fact-depth limit that starts at 3
and rises by one per whole-analysis quiescence, so **every `[any]`-carrying start edge is parked and
replayed forever**. Measured on the prototype: findings 0, a slower run, nothing reaching the solver.

**Change the inflation to `+= 10`.** The intent is right — `[any]` stands for an unbounded sequence
and should not be charged as one step — but 10_000 is not a cost, it is a sentinel that makes the
gate unsatisfiable. A charge of 10 keeps `[any]` genuinely expensive relative to a concrete step
while leaving it reachable, and then `edgeExceedLimit` needs no special case at all.

Two knock-on effects to handle in the same change:

- Anything using `depth > 10_000` as a "does this carry `[any]`" test breaks. That test should not
  exist — use the `containsAnyInThisOrDeepNodes` flag of §5.2. (The prototype's diagnostics use it, and so does the
  `anyPreserve` correction inside `edgeExceedLimit`.)
- `AccessPath.size` counts `[any]` as **1**, so the premise-side budget still under-charges exactly
  the premises that admit the deepest facts. Worth aligning the two charges.

### 5.2 Nested `[any]` must be collapsed, not asserted against

`AccessTreeAnySuffixMatcher` rejects `[any] -> … -> [any]` with a `check`, which aborts the whole
analysis. `concatToLeafAbstractNodes` can build exactly that shape: `getChild` re-prepends `[any]`
when the premise accessor is covered, so an `[any]`-carrying caller fact yields an `[any]`-carrying
delta, which is then grafted onto an `[any]`-carrying conclusion.

Under zero-or-more semantics (§3.5) the collapse is an **identity**, not an approximation:

```
[any].x.y.z.[any]   ==   [any]        for x, y, z all covered by [any]
```

so the invariant to maintain is: **no `[any]` is reachable from another `[any]` through a
covered-only path**.

There is no exception to carve out for an intervening uncovered accessor, because the obvious
candidate cannot occur: **`[any]` after a taint mark is impossible, and must be explicitly banned.**
`addParentIfPossible` only admits a mark above a bare leaf (`AccessTree.kt:453-459`):

```kotlin
accessor.isTaintMarkAccessor() -> {
    if (this == manager.finalNode || this == manager.abstractNode || this == manager.abstractFinalNode) {
        create(accessor, this)
    } else {
        null
    }
}
```

so nothing structured — an `[any]` least of all — can sit below a mark, and `[any].![m].[any]` is
unconstructible through that path. It is *not* currently enforced on the raw `create` constructor
used by `createAbstractNodeFromAccessors` and friends, which is why it should become an explicit
check rather than an emergent property. With that ban in place the collapse rule needs no qualifier:
any `[any]` reachable from another `[any]` collapses.

**Implementation.** Add a deep `containsAnyInThisOrDeepNodes` flag to `AccessNode`, computed at
construction exactly like the existing `containsStatic` (`AccessTree.kt:304`):

```kotlin
containsStatic = containsStatic || accessorNodes.any { it.containsStatic }
```

The name is deliberately long: `AccessNode` already has `containsAnyAccessor()`
(`AccessTree.kt:388-389`), which is `accessorIndex(ANY_ACCESSOR_IDX) >= 0` — **this node only**. The
two are easy to confuse and mean different things, so the deep one says so in its name.

`prependAnyAccessor` then checks the flag and collapses only when it is set — O(1) in the
overwhelmingly common case where it is not. It already does a one-level version of this
(`AccessTree.kt:589-597`: it merges an existing *direct* `[any]` child up rather than nesting); the
flag generalises that to "reachable through covered steps" and makes the check cheap enough to run
unconditionally.

Maintaining this as a representation invariant **subsumes constraint C3 of §3.4**: the concat path
cannot produce the illegal shape in the first place, so the matcher's `check` becomes unreachable
rather than needing to be relaxed.

## 6. Impact analysis

Paths below are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/`.

### 6.1 Already correct — no change needed

Most of the machinery is accessor-index-generic and handles `[any]` for free. This is the main reason
the design is tractable.

| component | why it already works |
|---|---|
| **`getChild` / `delta` / `contains` / `equalTo` / `filterStartsWith`** | all walk with `getChild`, which gives exactly the match rule of §3.1 |
| trie insert, `AccessBasedStorage.getOrCreateNode` (`:19-32`) | a raw `AccessorIdx` walk, no filtering or special-casing |
| `splitOnMatching` (`AccessTree.kt:506-533`) | walks with `getNodeByAccessor` — raw, literal, non-expanding, i.e. the structural semantics wanted |
| `createNodeFromReversedAp`, `createNodeFromAccessors`, `createAbstractNodeFromAccessors`, `splitDelta`'s prefix rebuild | use the raw `AccessNode`/`create` constructors; fully `[any]`-transparent |
| `AccessTreeIndexImpl` (`MethodTreeAccessPathSubscription.kt:239-282`) | built via `forEachAccessor`, already contains `[any]`-keyed nodes |
| `equals` / `hashCode` / `rebase` / `exclude` / `replaceExclusions` / `size` / `toList` | structurally kind-agnostic |
| **Serialization** | `TreeSerializer.kt:34-48, 63-82` writes an untagged flat accessor-id list; `AnyAccessor` has reserved wire id `0L` (`JIRSummariesFeature.kt:160, 401-406`); the reader rebuilds with the raw constructor, bypassing the drop site. **`[any]` round-trips today. Zero changes, no format version to bump.** |
| **Cross-unit transfer** | no serialization on any live cross-unit path — premises move as object references through `Edge.FactToFact.initialFactAp`. `ANY_ACCESSOR_IDX` is a compile-time constant, so index identity across units is free. |
| Type checking | `JIRFactTypeChecker` already has explicit `AnyAccessor` branches in `accessorActualType` (`:206`) and `AccessorFilter.checkAccessor` (`:86-92`) |
| The backend-agnostic layer (`ap/ifds/access/common/*`) | fully generic over the premise type; never inspects accessors |

### 6.2 `[any]` premises are *already* partially reachable

`AccessPath.prependAccessor` (`AccessPath.kt:60-69`) is asymmetric:

```kotlin
if (access == null) {
    return AccessPath(apManager, base, AccessNode(apManager, accessorIdx, next = null), exclusions)
}
val node = access.addParent(accessorIdx)     // <- only this path drops [any]
```

The empty-chain case builds the node **directly**, bypassing `addParent`. So
`mostAbstractInitialAp(base).prependAccessor(AnyAccessor)` already yields a premise `arg0.[any]`
today — reachable from `mkInitialAbstractAccessPath` (`taint/AccessPathCreationUtils.kt:33-40`) via
`taint/RulePreconditionUtils.kt:145`. Only *prefixing an existing chain* loses it. This is a latent
inconsistency, and it means some `[any]` premises are already flowing through the system unnoticed.

### 6.3 Required changes

| # | site | change | kind |
|---|---|---|---|
| 1 | `AccessPath.kt:296` (`AccessNode.addParent`) | Stop dropping `ANY_ACCESSOR_IDX`; collapse `[any].[any]` to one, mirroring `AccessTree.prependAnyAccessor` (`AccessTree.kt:589-597`). **This is *the* change.** | blocker |
| 2 | `AccessPath.kt:264-271` (`AccessNode.concat`) | Re-adds the left operand's accessors through `addParent`, so any `[any]` in it is **erased**. Live on the trace path (`MethodTraceResolver.kt:1601-1603`) — silent data loss, not a semantics choice. | blocker |
| 3 | `AccessPath.kt:336-343` (`limitFieldAccess`) | Walks *through* `[any]` when collapsing a repeated field, so prepending `a` onto `x.[any].a.b` yields `a.b` — dropping the `[any]` and changing meaning. Must stop at or preserve `[any]`. | blocker |
| 4 | `TIFA:188-196` | The abstraction descends the `[any]` edge but re-enqueues with `currentAp` **unchanged** — an independent second drop site. Must append `ANY_ACCESSOR_IDX`, or the representation exists but nothing can produce it. | blocker |
| 5 | `MethodInitialToFinalApSummaries.kt:97-117` + `:89-92` | *Not a blocker — resolved.* Id-edge subsumption drops `[any]` premises, and that is **correct**. See §6.4. | none |
| 6 | `ApManager.kt:55-59` (`AnyAccessorDisabled`) | *Not a blocker — resolved.* `unrollAccessor` throws, and prescan installs it (`TaintAnalyzer.kt:135`). But there are no `[any]` accessors during prescan, so it is unreachable there and the exception is the correct assertion. Leave as-is. Revisit only if `[any]` premises could ever survive `resetApManager` into the prescan manager. | none |
| 7 | `AccessPath.kt:141-164` (`splitDelta`) | Diverges from `delta`: an `isAbstract` escape hatch means premise `a.b.[any]` *does* match fact `arg0.a.b.*`. Needs the same strictness or the strong precondition leaks. | decision |
| 8 | `MethodInitialToFinalApSummaries.kt:43-46` | Replace the `allNodes()` blanket with a targeted rule. See §6.5. Requires widening `AccessBasedStorage.collectNodesContains` visibility (`:55`, private). | decision |
| 9 | `TIFA:263-265` | `TODO("Any after unroll-next is not supported yet")` becomes reachable — an `[any]` may now follow a mark, `[final]`, `[value]` or type accessor. | blocker |
| 10 | `MethodAnalyzer.edgeExceedLimit` | Must not treat the `[any]` `maxDepth` inflation as real depth (§5.1). Conversely, note `AccessPath.size` counts `[any]` as **1** while it stands for unbounded depth, so the delay budget *under*-charges exactly the premises admitting the deepest facts. | blocker |
| 11 | `AccessTreeAnySuffixMatcher` | Absorb nested `[any]` rather than asserting against it (§5.2). | blocker |
| 12 | `AccessPath.kt:172-176` (`AccessNode.filter`) | Exclusion sets never contain `AnyAccessor`, so an `[any]`-headed delta survives an exclusion `{f}` even though `[any]` covers `f`. Possible unsoundness. | decision |
| 13 | `taint/MethodSideEffectHandlerWithAnyAccessorRequestHandling.kt:48` | `kind.fact.getAllAccessors().isEmpty()` is the "premise is un-refined" guard. An `[any]`-bearing premise stops being "bare", so unfold requests stop being answered — **behaviour changes with no code edit**. | blocker |
| 14 | `taint/RulePreconditionUtils.kt:160-162` | `extractFactPaths` can emit `AnyAccessor` into `specialization`, which `prependAccessor` currently swallows — an existing correctness gap in `ContainsMarkOnAnyAccessorLiteral` preconditions. Fixing #1 fixes it for free, **and changes results**. | blocker |
| 15 | `AccessPath.kt:42-43` (`getAllAccessors`) | Would start returning `AnyAccessor`, while the fact side deliberately does the opposite (`AccessTree.kt:763-767`, `// note: always ignore any accessor`). The two would disagree. | decision |

### 6.4 Resolved: id-edge subsumption correctly drops `[any]` premises

`MethodTaintedSummariesIdStorage.getOrCreateChild` (`MethodInitialToFinalApSummaries.kt:97-117`)
throws `NodeSubsumedException` — caught as a silent drop at `:80-83` — when the accessor being
descended is *not* in the id edge's exclusion set. Since exclusion sets are only ever populated from
concrete accessors, `contains(AnyAccessor)` is always false and an `[any]` premise is therefore
always dropped.

**That is the right answer.** An id edge at `p` is an identity summary: everything below `p` passes
through unchanged. `p.[any].*` denotes a subset of `p.*`, so the id edge already covers it and the
separate premise adds nothing.

The apparent counter-example — an id edge `p.*{f}` that excludes `f`, against `p.[any]` which
*includes* `f`-prefixed paths — does not bite, because the exclusion never reaches the `[any]`.
`AccessTree.delta` filters the residual with `AccessNode.filter(exclusion)`
(`AccessTree.kt:193-195`, `:646-653`), which drops children whose accessor is in the set:

```kotlin
val transformedAccessors = transformAccessors(accessors, accessorNodes) { accessor, node ->
    with(manager) { node.takeIf { accessor.accessor !in exclusion } }
}
```

`AnyAccessor` is never in an exclusion set, so an `[any]`-headed residual survives the filter intact,
the id edge fires for the `[any]`-carrying caller fact, and the identity summary passes it through.
Nothing is lost.

This is an over-approximation rather than a precision win — the id edge passes through the whole
`[any]`, including the `f` part the exclusion meant to remove — but it is a false positive at worst,
never a false negative, and it is pre-existing behaviour independent of this feature.

### 6.5 Replacing the `allNodes()` blanket

`MethodInitialToFinalApSummaries.collectNodesContainsAccessor` (`:38-49`) returns the entire premise
subtree when the *caller fact's* accessor is `[any]`, discarding the pattern. It exists purely to
compensate for change #1: since premises can never hold `[any]`, `children.get(ANY_ACCESSOR_IDX)` is
always null, and without the blanket a whole-subtree-tainted caller fact would activate no deeper
premise at all — a soundness hole. (A second parallel workaround lives at `taint/Source.kt:44-48`,
which retries a lookup with the `[any]` stripped.)

Once premises can hold `[any]`, this becomes a two-arm rule: a **structural** arm descending into the
premise's `[any]` child, pattern-directed; and an **expansion** arm keeping concrete premises
reachable, restricted to accessors `[any]` can actually cover. The result is a strict subset of
today's `allNodes()`.

Two defects worth fixing **independently of this feature**:

- It ignores `isCoveredByAny`, activating premises keyed by taint-mark, type-info, static, `[value]`
  and `[final]` accessors that the `[any]` provably cannot reach — pure-loss over-approximation.
- It produces duplicates (`this` is added at `AccessBasedStorage.kt:57` and again as `allNodes()`'s
  first element; `filterContains` never deduplicates), yielding duplicate `FactToFact` edges.

Cost today: `allNodes()` is an eager O(n) traversal with O(n) allocation and no caching
(`AccessBasedStorage.kt:76-92`). Measured on the prototype it is **not** currently a bottleneck
(1.25 M calls, 88 ms) — but that is *because* the cap shrank the tries.

### 6.6 Scope: which backends

| backend | status |
|---|---|
| **Tree** (`ApMode.Tree`, default) | the target |
| **Automata** | **hard blocker** — four `check(accessor !is AnyAccessor)` in `AccessGraphInitialFactAp.kt:32, 40, 45, 50`. Note it independently implements something close to this design for facts (§2.7). |
| **Cactus** | `AccessPathWithCycles.prependAccessor` (`:59-62`) would accept `[any]` silently; the rest of the class is stubs. No `[any]` support anywhere. |

Recommendation: gate the feature on `ApMode.Tree`.

Prescan needs no change: it installs `TreeApManager(AnyAccessorDisabled, …)` whose `unrollAccessor`
throws, but there are no `[any]` accessors in that phase, so the assertion is unreachable and correct.
The one thing to keep an eye on is `resetApManager`, which swaps the manager between prescan and full
scan while `AccessPath` instances hold a reference to theirs.

### 6.7 Pre-existing asymmetry the feature will expose

`FactSideEffectSummariesTreeApStorage` (`:112`) and `SideEffectRequirementTreeApStorage` (`:59`) use
`filterContains` with **no** `[any]` override, so they have no expansion arm: a caller `[any]` fact
does not activate concrete side-effect premises today. Once premises can hold `[any]` these storages
get a literal `[any]`-to-`[any]` match for free, which makes the missing expansion arm visible.

### 6.8 Interner cardinality

`AccessPathInterner` cannot currently distinguish two premises differing only by an `[any]`, because
the collapse already happened before they arrive. Fixing the drops increases interner cardinality;
expect index and BitSet growth in `AccessPathInterner.allIndices` (`:36`) and its consumers.

## 7. Risks and open questions

### R1. `[any]` facts are more expensive per operation than concrete facts

This is the central risk, and it is measured rather than hypothetical. Keeping `[any]` symbolic moves
cost from premise *enumeration* to fact *representation*. On the prototype at limit 100, facts
carrying `[any]` went 1,835 -> 45,845, and although premise lookup got 8x cheaper, summary
*application* got 3.4x more expensive:

| timer | baseline | capped |
|---|---:|---:|
| `summary.subscribe.lookup` | 7,934 ms | **1,022 ms** |
| `summary.subscribe.apply` | 71,644 ms | 246,754 ms |
| `static.subscribe` | 45,778 ms | 237,178 ms |

Root cause is §3.4 — unbounded tree depth below `[any]`. **The optional optimisation is therefore not
really optional if the goal is a net win**; it is what converts a correct feature into a fast one.
Two candidate causes were investigated and eliminated:

- The `[any]` premise-lookup amplifier (`collectNodesContainsAccessor` returning `allNodes()`):
  1.25 M calls, **88 ms**, ~1.2 nodes per call. Not a factor once the cap has shrunk the tries.
- `AccessTreeAnySuffixMatcher` rebuilt per merge: 91,002,062 constructions, 143 s. Real, but only
  ~27% of the cost. It is immutable and a pure function of its suffix node, so memoising it on the
  node cut it to 30.6 M / 35 s. Disabling it outright was also measured — neutral on the baseline
  (findings intact, confirming it is pure redundancy elimination) but *worse* under the cap, because
  the fold is what keeps `[any]` trees small.

### R1b. Two false-positive vectors from the concat optimisation

Both are over-approximation — neither can cause a false negative — but both should be measured.

1. **Depth promotion of marks.** `[any].x.![m]` does not answer a mark read at the base;
   `[any].![m]` does. So a deep field-level mark becomes a base-level whole-object mark, and a
   non-starred sink reading the mark at exactly the base position can newly fire. Mitigating context:
   this is the same shape a `$*VAR` source already seeds, `TaintSourceActionPreconditionEvaluator`
   deliberately falls back to the base position for `X.[any]` (`taint/Source.kt:44-48`), and
   `FactCleanerContractTest:110-121` pins it as intended `[any]` semantics. It is a legitimate
   widening, but it is *the* FP vector to watch.
2. **Sanitizer depth claims.** Violating constraint C2 (§3.4) silently defeats `DeepAccessorExclusion`
   depth-1 claims. Correct ordering makes this a non-issue; `AnyFieldMarkExclusionTest:192-203` pins
   the depth-0/depth-1 distinction and would catch it.

### R2. The cap's limit is a precision dial with no principled default

Too low and precision suffers; too high and the explosion is not contained. The prototype's evidence
is muddied because conductor does not converge in *any* arm, so its finding counts reflect how far a
run got, not what is findable. **Choosing the default requires a workload that converges** — see §8.

### R3. Interaction with the fact-depth delay gate

`MethodAnalyzer.edgeExceedLimit` must be taught that a `[any]`-carrying fact's inflated `maxDepth` is
not real depth (§5.1), or the feature is inert. Any fix must not accidentally disable the gate for
genuinely deep facts, since that gate is what staggers the analysis.

### R4. Nested `[any]`

`[any].[any]` is semantically `[any]` and must be absorbed rather than asserted against (§5.2). The
absorption already exists on the *prepend* path (`prependAnyAccessor`, `AccessTree.kt:589-597`) but
not on the concat/merge path.

### R5. Open: should `[any]` premises be emitted always, or only past the cap?

Emitting them always would remove unrolling entirely — simplest, cheapest, least precise. Emitting
them only past the cap keeps today's precision for the overwhelming majority of bases (at limit 100
on conductor, exactly **three** bases are ever cut) and confines the new behaviour to the pathological
tail. This design proposes the latter, but the former is worth measuring as an ablation once the
feature works, because it would delete the round loop, `unrollAnyAccessors`, and the `unrolled` memo
outright.

### R6. Open: `abstractNextAccessPath` has an unimplemented `[any]` case

`TODO("Any after unroll-next is not supported yet")` (TIFA:263-265). Allowing `[any]` in premises
makes this path more reachable, since an `[any]` may now follow a mark or type-info accessor. This
must be resolved before the feature can ship.

### R7. Dead branch adjacent to the change

`state.added.isFinal` (TIFA:198-201) passes `emptyNode` into a helper that cannot emit, so a premise
`base.<field>.$` is unreachable today and untested. It sits directly in the code being modified.
Worth fixing or deleting deliberately rather than preserving by accident.

---

## 8. Validation plan

The single most important lesson from the prototype: **conductor cannot validate correctness**. No
arm converges — baseline included — so its finding count measures how far a run got before OOM or
timeout, not what is findable. Correctness and performance need different workloads.

### 8.1 Correctness — must be loss-free

1. **Engine and rule test suites with the cap forced to its most aggressive setting** (`limit = 1`,
   cut after the very first unroll). This is the strongest available loss-freeness signal because it
   forces the new path everywhere. On the prototype: `:opentaint-jvm-dataflow:test` **98 passed / 0
   failed** and `:opentaint-java-querylang:test` **237 passed / 0 failed**.
2. **A converging project, findings diffed exactly.** `opentaint-test-openmrs-core` and
   `opentaint-test-tms` are available alongside conductor and thingsboard and are the right size for
   an exact SARIF diff (rule id + location), baseline vs capped, at several limits.
3. **Targeted unit tests** for the new premise shapes, added to `InitialFactAbstractionTest`:
   `(arg0.[any], arg0.[any].*)` as an identity pair; `delta` of an `[any]`-free fact against an
   `[any]` premise is empty; `delta` of an `[any]`-carrying fact is the subtree below it; a mark
   below an `[any]` produces a premise that names the mark.
4. **A concat/absorption test suite** if §3.4 is implemented. `AnyFieldMarkExclusionTest` is the
   right home — it is the only unit test of `FinalFactAp.concat` — but note that **no existing test
   grafts a delta below an `[any]` edge**, so nothing currently pins the behaviour being changed.
   Build a conclusion `base.[any].*` and assert each row of the §3.4 table, plus a depth-1
   `DeepAccessorExclusion` claim combined with a covered prefix asserting the claim still bites (C2).
   The fully-covered row must assert the result stays abstract and is **not dropped** (C1).
5. **End-to-end precision net**: `StarOperatorTest` (15+ tests over `$*` sources/sinks/sanitizers,
   including `star nested wrapper sanitizer - deep exclusion composes across summary levels`),
   `Phase3StarSourceGetterTest`, `StarPatternNotCoincidenceTest`, `StarPatternNotFieldOnlyTest`, and
   the Go-side `GoStarOperatorEmitTest`. These are the tests most likely to move on the R1b vectors.

### 8.2 Performance

Report `rc` (0 OK / 253 OOM / 254 TIMEOUT / 252 EXCEPTION), wall, peak RSS, max progress, findings,
live heap after full GC, and the `MemoryManager` high-threshold crossing count — the last is the best
early OOM predictor and was the clearest signal in the prototype (16 crossings baseline vs 1 capped).

Counters to watch: `abstract.facts.emitted`, `anylife.seed.withany`, `summary.subscribe.lookup` vs
`summary.subscribe.apply`, and fact size/depth histograms.

Workloads: conductor (OOM-bound), thingsboard (timeout-bound, 14 findings), plus openmrs and tms as
converging controls. **ThingsBoard has not yet been measured on any capped arm** and is the most
important missing datapoint, because it is the one large workload whose baseline produces a stable
finding count.

### 8.3 Rollout

Default off behind a system property, as in the prototype (`-Dopentaint.anyUnrollLimit=-1`). Turn on
by default only once §8.1 is green and a limit is chosen from §8.2 on a converging workload.

---

## 9. Prototype evidence

`saloed/12-any-unroll-budget` @ `a6e5be532` implements the *pre-`[any]`-premise* variant: the cap plus
an explicit covered/not-covered frontier split, because premises could not hold `[any]`. Its results
are what this design is built on.

| | baseline | capped (limit 100) |
|---|---:|---:|
| `abstract.facts.emitted` | 891,654 | **21,828** |
| `abstract.anybranch.descents` | 22,278,704 | **109,254** |
| `summary.premise.tests` | 5,320,752 | **250,442** |
| methods >1024 premises | 36 | **0** |
| methods >16384 premises | 5 | **0** |

Bases cut at limit 100: **three**, and they are exactly the methods an independent provenance trace
had already named — `WorkflowServiceImpl#rerunWorkflow`, `WorkflowExecutorOps#rerun`,
`WorkflowExecutorOps#rerunWF`.

Two variants were measured and rejected, both of which collapse the frontier instead of preserving
what `[any]` cannot express:

| variant | findings | note |
|---|---|---|
| frontier -> `prefix.[any].*` | **0** | also inert: every edge parked by the depth gate |
| frontier -> `prefix.*` | **0** | mark dropped; also re-explodes downstream (premises 515,707) |
| covered/not-covered split | 2 in tests, unstable on conductor | the shipped prototype |

The `[any]`-in-premise design in this document supersedes the split: it obtains the same property
from the ordinary walk rather than from a special case.

---

## 10. Implementation order

The changes are heavily interdependent — several are silently inert or actively destructive on their
own. Suggested sequencing, each step independently testable:

1. **Unblock the environment.** Change the `maxDepth` inflation from 10_000 to 10 (§5.1), ban
   `[any]` below a taint mark, and add the deep `containsAnyInThisOrDeepNodes` flag with the collapse
   invariant (§5.2), which makes the nested-`[any]`
   assertion unreachable. Nothing changes behaviourally yet, but `[any]`-carrying facts stop being
   parked or fatal.
2. **The concat optimisation (§3.4)** — with C0-C4. Independently valuable: it bounds tree growth
   below `[any]` for facts that already exist today, and C0 turns both limiters into O(1) no-ops on
   the hottest path in the engine. Ship and measure this alone first; §5.2 has already removed the
   nested-`[any]` shape it would otherwise have to handle.
3. **Make `[any]` representable in a premise**: `addParent` (#1), `concat` (#2), `limitFieldAccess`
   (#3), `splitDelta` (#7). Still no producer, so behaviour changes only for the already-reachable
   paths of §6.2 — audit `RulePreconditionUtils` (#14) and
   `MethodSideEffectHandlerWithAnyAccessorRequestHandling` (#13) here.
4. **Fix the premise lookup rule**: the `allNodes()` blanket (#8). Id-edge subsumption (#5) needs
   no change — it correctly drops `[any]` premises as already covered (§6.4).
5. **Make the abstraction produce them**: `TIFA` (#4) plus the `TODO` at `TIFA:263-265` (#9).
6. **Add the cap** (§3.3) and choose its limit on a converging workload.

Steps 1-2 are worth doing regardless of whether the rest lands.

## 11. Design follow-up: pack `AccessNode`'s flags into one byte

`AccessTree.AccessNode` carries its booleans as separate fields (`AccessTree.kt:261-272`):

```kotlin
@JvmField val interned: Boolean,
@JvmField val isAbstract: Boolean,
@JvmField val isFinal: Boolean,
…
@JvmField val containsStatic: Boolean
```

plus `containsAnyInThisOrDeepNodes` from §5.2, which brings it to five. Replace them with a single `Byte` and
bit-accessor properties:

```kotlin
@JvmField val flags: Byte

val isAbstract: Boolean get() = flags and ABSTRACT != 0
val isFinal: Boolean get() = flags and FINAL != 0
…
```

The motivation is heap, and heap is the binding constraint on the workload this whole design targets
— conductor OOMs at 8 GB, and live heap after full GC is 7377 M. `AccessNode` is the single most
numerous object in the analysis (the prototype measured facts averaging 43 nodes each across
2.6 M abstraction calls, and 22,867 individual facts exceeding 1000 nodes). Five booleans occupy five
bytes plus alignment padding in the JVM object layout; one byte plus accessors removes several bytes
per node, which at these counts is worth tens of megabytes.

Two notes:

- Do this **after** `containsAnyInThisOrDeepNodes` exists, so the flag set is stable and the
  change is made once.
- Keep the properties `@JvmField`-free and `inline`-friendly; these are read on the hottest paths in
  the engine (`getChild`, `mergeAdd`, `concatToLeafAbstractNodes`), so the accessors must fold away.
  Verify with a before/after heap measurement rather than assuming — the prototype's benchmark
  harness already reports live-heap-after-full-GC and the `MemoryManager` threshold-crossing count.

This is independent of the rest of the design and can land at any point.

## 12. Free wins available independently

These are defects found while scoping, unrelated to whether this feature ships:

- `allNodes()` ignores `isCoveredByAny`, activating premises keyed by mark/type-info/static/`[value]`/
  `[final]` accessors that the `[any]` provably cannot reach (§6.5).
- `filterContains` never deduplicates, and the `[any]` blanket double-adds the current node — yielding
  duplicate `FactToFact` edges (§6.5).
- `AccessTreeAnySuffixMatcher` is immutable and a pure function of its suffix node, yet rebuilt per
  merge: 91,002,062 constructions / 143 s on conductor. Memoising it on the node cuts it to
  30.6 M / 35 s. (Already done on the prototype branch.)
- `AccessPath.prependAccessor` is asymmetric — the empty-chain case bypasses `addParent` and already
  preserves `[any]` (§6.2). Either behaviour may be right; the inconsistency is not.
- `TIFA:198-201` (`state.added.isFinal`) passes `emptyNode` into a helper that cannot emit, so a
  premise `base.<field>.$` is unreachable and untested. Dead branch in the code being modified.
