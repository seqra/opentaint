# The `[any]` unroll manager

A budget that travels with the `[any]` it bounds.

- **Branch**: design targets `saloed/14-any-premise-impl` @ `50ccd990f`.
- **Scope**: the tree access-path backend (`ApMode.Tree`, the default). All changes stay inside
  `ap/ifds/access/tree/`; no signature outside it changes. §12.4 covers the other backends.
- **Supersedes**: `2026-08-24-any-unroll-limit-design.md` (the per-fact carried limit), and the
  per-`(MethodEntryPoint, AccessPathBase)` counter it in turn superseded.

Path abbreviations: **AT** = `access/tree/AccessTree.kt`, **AP** = `access/tree/AccessPath.kt`,
**TIFA** = `access/tree/TreeInitialFactAbstraction.kt`, **SUB** =
`access/tree/MethodTreeAccessPathSubscription.kt`, **MIFAS** =
`access/tree/MethodInitialToFinalApSummaries.kt`, all under
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/ap/ifds/`.

**Revision — edge-case validation pass.** The lifecycle map, the TIFA integration, the storage layer
and every `AccessNode`-producing site in AT were audited against the design. Eight defects were found
and fixed in place; nothing was appended as errata. In order of consequence:

| what was wrong | now |
|---|---|
| the branch invariant was never stated, so the bound was `Lᵈ`, not `L` | §2.4 |
| `parentEdgeIsAny == false` was read as "no `[any]` above" — it is a one-level memory | §4.4 — superseded by revision 3, which normalises at install instead of threading |
| `filterStartsWith` AT:1750 and `reconstructRemainder` AT:721 re-create `[any]` edges raw; both were absent from the site table. AT:1750 is 657,633 events at cap 0 | §4.1 |
| the manager had no notion of its origin, so `total` was per-position and §1.2's branching returned | §2 — the state carries its dag, so the pot is reached rather than chased |
| the TIFA unroll was to "share" the parent id; it consumes a step, so it must advance to the child | §6.1 |
| TIFA's own emissions were to mint per premise — the §1.1b failure through a side door | §6.3: inherit the walk's governing state |
| `find` was to be stored *and* compared, which makes `hashCode` change under a union | §3.4: the stored reference at compare time, `find` at build time and in the guard |
| §5.3's sketch called `isCoveredByAnyOrFalse`, which does not exist and must not | §5.3: probe for the edge first |

Two claims the audit **confirmed** rather than corrected: no `AccessNode` crosses a `TreeApManager`
boundary (§9.1), and `isCoveredByAny(ANY_ACCESSOR_IDX)` is `false`, so the `[any]`-zero-times descent
is free (§5.3). One new termination question was opened and answered: §8.5.

**Revision 2 — the structure is an automaton, not a trie.** A second pass, driven by five questions
about counting, nesting, dormancy, loop convergence and memory, changed the representation itself:

| finding | consequence |
|---|---|
| a state can be reached by many accessor sequences, so counting states under-reports the population | **§2.6**: charge `pathCount`, not 1, maintained incrementally |
| an ancestor–descendant union creates a **cycle**, and a program loop produces exactly that union | **§2.5**: the structure is cyclic by necessity; the cycle *is* the loop's fixed point, and breaking it breaks termination |
| `total` as "number of accepted words" is `∞` on a cycle | **§2.6**: incremental, saturating `pathCount`; nothing is ever computed by traversing the automaton |
| a state needs an origin *and* a position, and states from different automata must not merge directly | **§3**: the state carries its dag, and `mergeStates` has a same-dag precondition that the caller establishes by fusing dags first |
| `[any].f.[any]` was believed impossible by construction | **§2.4**: true only for *covered* `f`, and only when `prependAnyAccessor` is called. `AnyAccessorCollapseTest.kt:143-153` asserts `[any].{Box}.[any].$` **survives** |
| dormant ids on `AccessNode` would break the one `===` the loop fixpoint rests on | **§3.4**: dormancy lives on the `AccessTree` wrapper, which is thin, uninterned and transient. One file needs it |
| "an id change is a non-empty delta" | **§3.5**: reversed. Receiver-preferred unions make the term vacuous, and a tightened budget needs no re-propagation. But the union is a side effect that must not be skipped |
| memory | **§3.8**: bounded by `origins × (L+1)`. The witness's 40k mints would be both a useless bound and a large heap, so memory and budget are one measurement |

**Revision 3 — force the collapse, and stop leaking ids.** A third pass on two points:

| finding | consequence |
|---|---|
| `[any].<covered>.[any]` collapses only inside `prependAnyAccessor`, so every other route preserves it — and two live operations actively **produce** it: the concat graft through `limitFieldAccess` (AT:1676 → AT:1700), and `removeAllAccessorChains` over an SCC containing an uncovered accessor | **§4.7**: normalise at the three sites that install an `[any]` edge (AT:2195, AT:2221, AT:2018). A rewrite, not a `check`; covered-only chain; the tail must be a literal `[any]`, never `.*` |
| the collapse is not an identity, contrary to AT:776-779 and `2026-08-21-any-premise-design.md:422` | **§8.2**: `[any].f.[any].g ⊊ [any].g` — a monotone coarsening. Sound, but it has a precision cost that has to be measured, hence its own implementation step and its own SARIF gate |
| forcing the collapse makes the graft threading redundant | **§2.4, §4.4**: `governingAnyId` on the concat recursion is **removed**. `concat` rebuilds the receiver's spine, so the outer edge is re-installed with the graft in place and one normalisation sees the whole subtree |
| int ids in columnar arrays are never reclaimed, and the overflow valve survived a leak rather than removing one | **§2, §3**: states and dags become objects with pointer DSU links, so a merged-away state is collected once nothing holds it. No id space, no `AnyIdDsu` class, no valve |
| a `WeakReference` + `ReferenceQueue` drain would work but is more machinery than needed | **§3.1**: plain reachability suffices, because nothing keeps a registry of states — checked: every counter in the engine is accumulated eagerly into `MethodStats`, and nothing iterates facts or nodes |
| "dead automata are collected" over-claims | **§3.8**: storages are merge-monotone and never delete, so states that reach a stored fact live for the phase. What reclamation recovers is the **transient mint** — precisely the case worth fixing, and not the whole population |
| hoisting under an `[any]` might need `absorbedAnyStep`-style depth bookkeeping for `DeepAccessorExclusion` | **§4.7**: it does not, for three reasons visible in the code — checked rather than assumed, since this is where the change would have been quietly unsound |

**Revision 4 — two notes.** `[any]` is `Σ*`, so the collapse is the containment `Σ* ⊇ Σ*·f·Σ*` for
`f ∈ Σ` (§8.2) — which makes the covered-only guard a consequence rather than a rule, and shows that
"at most one `[any]` per path" is sound only per *covered-only stretch* of a path. And the DSU's
`parent` is written concurrently, whose interesting failure is a **cycle in the forest** rather than a
lost update (§3.3).

Checking the associated claim — that the analyzer never builds `[any].X.[any]` for uncovered `X` —
confirmed it for all seven, and found that the three supporting mechanisms are not equally solid
(§4.7): marks are enforced by `check(node.isStructurelessLeaf)`, statics by the subtree-wide
`containsStatic` guard, `[final]` is not an edge, `[value]` is dead code — but **type-info is enforced
by nothing**, and holds only because both front ends prepend onto a fresh `$`. That is now R28.

---

## 1. Three shapes that failed, and exactly why

This design is the fourth attempt. Each previous one failed for a *different, identified* reason, and
the manager exists because it is the first shape that answers all three at once. Anyone tempted to
simplify it back toward one of these should read this section first.

### 1.1 A per-context counter — only one channel charged

`TreeInitialFactAbstraction.unrolledFactCount` (TIFA:401-408) counts unrolls per
`(method entry point, access-path base)`. It is reachable **only** from `unrollAnyAccessors`
(TIFA:125). The other channel that materialises concrete accessors — the spine rebuild in
`AccessNode.filterStartsWith` (AT:1750) — never touches it.

Instrumented on the conductor witness: at no cap, **16,249 accounted unrolls and 0 unaccounted**; at
cap 0, **0 accounted and 482,233 unaccounted**. The two paths are *alternatives*. Capping the counter
does not remove work, it **diverts** it.

`AnyPrependDiag` measured the diversion per site. Counting events that made the shallowest `[any]`
strictly deeper, on the same witness:

| site | uncapped | cap 0 | factor |
|---|---:|---:|---:|
| `addParent/unroll` + `unroll` (the unroller) | 127,076 | **0** | — |
| `concat` | 9,898 | **1,170,752** | 118× |
| `filterStartsWith` | 9,321 | **657,633** | 71× |
| `addParent/alias` | 2,542 | 33,578 | 13× |
| total (real events) | ~149,000 | **~1,872,000** | **12×** |

Capping the one channel the counter can see **increased total materialisation twelvefold.**

### 1.1b The budget was also keyed far too finely

`UnacctDiag` counted the budgets themselves: **7,347 distinct `(entry point, base)` pairs** on a
single-rule, single-entry-point witness (9,830 budget objects). With `ANY_UNROLL_LIMIT = 100` that is
an effective global allowance of ~735,000 unrolls. The cap was not weak because 100 is a large number;
it was weak because it was multiplied by seven thousand independent buckets.

Any replacement has to be keyed by something whose cardinality is small and *meaningful*. §2 keys by
`[any]` origin, of which the conductor witness has on the order of ten — the `$*` whole-object source
markers — rather than thousands.

### 1.2 A per-fact carried limit — bounds depth, not population

Attaching a remaining budget to the fact's root node and decrementing it on growth fails on
branching. With `X = arg.[any].*` at limit 10:

```
Y = read(X, a)   ->  Y.limit = 9
Z = read(X, b)   ->  Z.limit = 9      // two unrolls performed, one charged to each
```

The budget forks with the derivation, so `L` bounds the length of any single chain while the
population still grows like `breadth^L`. A budget that bounds an explosion has to be **shared**
between the derivations that spend it.

### 1.3 A read-side predicate — structurally blind to most of the phenomenon

Prototype `saloed/30-charge-hidden-unroll` charged the `filterStartsWith` rebuild against a budget,
using this test to detect a covered read:

```kotlin
filteredTreeNode.containsAnyAccessor()
    && manager.isCoveredByAny(accessor)
    && filteredTreeNode.getNodeByAccessor(accessor) == null
```

Conductor, four arms (off / 100 / 10 / 0): `rc=254` in all four, 901–929 s, 14,192–15,196 premises,
**2 findings in all four**. `charged=103` against `limit=100` is the tell — at most two budgets ever
reached the predicate at all, against ~650k spine rebuilds. Three independent narrowings:

- **It requires the node at that link to own an `[any]` edge.** In the diverging loop the fact is
  `X.<concrete prefix>.[any]` with the `[any]` **terminal**, so every premise link landing inside the
  concrete prefix fails the test. Only a premise running *past* the concrete depth is ever visible.
- **`getNodeByAccessor(a) == null` is first-time-only.** Once a deepened fact merges back into the
  subscription storage, that node carries the concrete `a` edge *alongside* its `[any]`, so the test
  is false forever after — while `getChild(a)` still merges the `[any]` back in and the spine still
  grows. It charges the first occurrence; **the explosion is the repetition.**
- **A nested `[any]` disqualifies the whole walk.** `isCoveredByAny(ANY_ACCESSOR_IDX)` is false by
  design, and on this branch `[any]` is a first-class premise accessor — so `[any]`-carrying premises
  are structurally unbudgetable by that predicate.

The measure that produced the real number, 657,633, was `AnyPrependDiag`, which asks of the
**result**: did the shallowest `[any]` get strictly deeper? And it splits provenance:

- **`fromAny`** — a concrete accessor went in front of an existing `[any]`;
- **`fromNothing`** — an `[any]`-free concrete prefix had an `[any]` attached at its *leaf*, which is
  what summary application does through `AccessTree.concat`.

**No predicate keyed on the read can see `fromNothing` at all.** That is a third channel, invisible to
both §1.1 and §1.3.

### 1.4 What the three failures jointly require

| failure | requirement |
|---|---|
| §1.1 diversion | every channel that materialises an accessor must charge the *same* budget |
| §1.2 branching | the budget must be **shared** across derivations, not forked with them |
| §1.3 blindness | the charged event must be a property of the **emitted structure**, not of the operation that emitted it |

The manager satisfies all three. §5.1 gets the third by charging at `getChild`'s covered arm — the
single point where an accessor is ever synthesised out of an `[any]` — so every caller is covered at
once rather than one at a time. That is not quite "no enumeration": §5.2 still has to separate
fact-building callers from boolean queries. But that is a ten-function list about call sites, not a
guess about tree shapes, and it fails safe in the direction that costs precision rather than the bound.

---

## 2. The design in one page

An **`[any]` unroll manager** is a small mutable object owned by an `[any]` occurrence in a fact tree.
It holds the set of concrete accessor sequences that have been materialised out of that `[any]`,
represented as a **deterministic automaton** — one successor per accessor — and the size of that set
is the budget measure.

Not a trie, and not even a DAG: §2.5 shows the structure **must** be allowed to become cyclic, and
that the cycle is exactly how a program loop reaches its fixed point. Everything below is designed so
that no operation ever has to traverse it.

The node **points at a state object**, and the whole structure is ordinary reachable heap:

```kotlin
class AnyUnrollState(
    @JvmField val id: Int,                  // dense, for hashing only -- see §3.4
    @JvmField val dag: AnyUnrollDag,        // strong: the pot this state spends from
) {
    @Volatile @JvmField var parent: AnyUnrollState? = null    // DSU link; null == representative
    @JvmField var pathCount: Int = 1                          // §2.6, saturating
    @JvmField var children: ConcurrentReadSafeInt2ObjectMap<AnyUnrollState>? = null   // transitions
}

class AnyUnrollDag(@JvmField val id: Int) {
    @Volatile @JvmField var parent: AnyUnrollDag? = null      // DSU link
    @JvmField var total: Int = 0                              // the budget pot
}

AccessNode.anyId : AnyUnrollState?         // null = none
```

`ConcurrentReadSafeInt2ObjectMap` (`util/ConcurrentReadSafeInt2ObjectMap.java`) is the house type for
exactly this access pattern — it captures the backing arrays and retries, so reads are lock-free while
writes are synchronized. `AccessBasedStorage` already keys its children with it.

Four things follow from this shape, and each is load-bearing.

**The DSU is pointer-based, so there is no id space to run out of.** `find` walks `parent` with path
halving. A merged-away state holds its representative; a representative does not hold the states merged
into it. Three earlier problems disappear at once: no segmented array that must never be copied, no
ceiling on how many states may be minted, and — the point of the change — **no leak**.

**Dead states are reclaimed by the garbage collector, with no registry and no reference queue.** A
state is reachable exactly when a live `AccessNode` references it, a live state has a transition to it,
or it is a live state's DSU representative. Nothing keeps a global index of states, so there is nothing
to drain — §3.8 bounds what this actually recovers, which is narrower than it first appears.

**A state keeps its successors alive, and that is correct rather than a leak.** The transitions *are*
the record of what has been materialised, and R4's "reuse it free" — the idempotence the whole design
rests on — needs them present. What dies is a state nothing can reach any more.

**A reference costs the same as an `Int`.** `AccessNode` is 53 bytes of content, 56 aligned; `+4` for a
compressed oop gives 57 → **64**, the same as the packed `Long` an earlier draft used. The state object
itself is ~32 bytes plus a transition map when non-empty, so the trade against columnar arrays is
"~32 bytes per **live** state" against "8 bytes per **ever-minted** state". §3.8 does that arithmetic
and says when each wins.

Five rules govern the lifecycle:

| # | event | rule |
|---|---|---|
| R1 | an `[any]` edge is **created** where none existed | mint a fresh `AnyUnrollDag` and its root `AnyUnrollState`, `pathCount = 1`, `total = 0` (§4.1 lists the sites) |
| R2 | an `[any]` is prepended onto a tree that **already has** one or more `[any]`s | union all of them and reuse the result — never mint (§2.4) |
| R3 | two `[any]` **tree edges become one** | union their states (§3.3); if the dags differ, fuse the dags first |
| R4 | an accessor `a` is **read through** an `[any]` | if the `a`-transition exists, reuse it **free**; otherwise mint a successor and charge |
| R5 | the **charge** for a new transition out of state `n` | `dag.total += n.pathCount`, **not** `+= 1` (§2.6) |

R4 is where the budget is consulted and R5 is where it is spent. `total` lives at the dag, so every
state descended from one `[any]` origin spends from one pot — that is §1.2's requirement. R4's
"reuse it free" is what makes re-derivation cost nothing, which is the property a plain counter could
never have and the reason the structure exists at all.

Two consequences of R4 that are easy to get wrong:

- **The automaton records derivation order, not tree depth.** R2 can put a state at automaton depth 3
  onto an `[any]` edge at tree depth 0. That is correct and desirable: a state is a canonical name for
  *the sequence of reads that produced this `[any]`*, which is exactly what must not be paid for twice.
- **A read that finds an existing transition charges nothing and mints nothing.** This is not an
  optimisation; it is the termination argument (§2.5).

### 2.1 Ownership: `TreeApManager` allocates and unions

Allocation (R1) and union (R3) are `TreeApManager`'s responsibility, not the nodes'. It is the single
object every tree-backend site already holds — `TreeInitialFactAbstraction(this)` at
`TreeApManager.kt:54` and `MethodTreeAccessPathSubscription(this)` at `:77` — and it is the only
common ancestor of the two spend sites, which live under different owners (TIFA under the callee's
`NormalMethodAnalyzer`, the subscription under the caller's `SummaryEdgeSubscriptionManager`).

The pot is reached as `node.anyId.find().dag.find().total` — three pointer hops, no table — and every
node pointing anywhere into the automaton reaches the same pot (§3.1).

### 2.2 The union is a product, not a root repoint — and it has two layers

This is the part that is easy to get wrong. The structure must stay **deterministic**: from any state,
one accessor leads to exactly one successor. A DSU union that merely repoints one root at the other
leaves two successors for the same accessor — an NFA — and then every lookup has to explore a set of
states, re-derivation stops being free, and the whole idea collapses.

The id-level `union` is what *names* the result; the state-level product is what keeps it
deterministic. Both are `TreeApManager`'s job and they happen together:

```
mergeStates(x, y):                                   // PRECONDITION: same dag (see below)
    x = find(x); y = find(y)
    if x === y: return x
    if memo[(x, y)] exists: return it                 // REQUIRED -- breaks cycles (§2.5)
    y.parent = x                                      // receiver wins (§3.2)
    memo[(x, y)] = x
    x.pathCount = sat(x.pathCount + y.pathCount)
    for each accessor a with a transition out of x or y:
        x.children[a] = mergeStates(x.children[a], y.children[a])   // one successor per accessor
    return x
```

Structurally this is what `AccessTree` already does for trees: `mergeNodeLoop` (AT:1231-1282) is an
explicit-stack merge with an identity-keyed memo (`AccessNodeMergePair`, AT:1122-1132). The same shape
applies here, and the same reason for the explicit stack applies — these structures get deep enough
that recursion is a liability, and here they can also be *cyclic*.

Note `y.parent = x` is the whole DSU union: no array, no id allocation, and `y` becomes garbage the
moment nothing else refers to it (§3.8).

**Two layers, and states from different automata must never be merged directly.** A state belongs to
one dag, so `mergeStates` carries a precondition, and the caller establishes it:

```
union(a, b):
    da = find(a.dag);  db = find(b.dag)
    if da !== db:
        db.parent = da
        da.total += db.total                          // pots combine, §2.6
        mergeStates(rootStateOf(da), rootStateOf(db)) // "2 automata in, 1 automaton out"
    return mergeStates(a, b)
```

Fusing the dags means merging their **start states** — two automata before, one after — so the result
is a single deterministic structure rather than two with a shared pot. Only then are the two operand
states in one automaton and mergeable.

That is the one thing the dag must retain: a reference to its root state, so it can be reached for a
fusion. It costs one state per live dag and it closes a reference cycle (dag → root → dag) that the
collector handles without help.

**Where a union comes from.** The clean case is that a manager union is the *shadow* of a tree-edge
merge: whenever two `[any]` edges in a fact tree become one edge, their managers union. That covers the
ordinary position-wise merge, the fold-to-`[any]` trimming, and the collapse of a nested `[any]` into
the one above it — all three are "two `[any]` edges became one", and all three need no separate rule.

It is not the only case, and §2.4 shows why: on a branch where two `[any]` edges coexist without ever
merging — the shape `[any].{Box}.[any]`, which a passing test pins as *legal* — the managers must
still be unioned, because the population under them is multiplicative. So the rule is "two `[any]`s on
one branch share a pot", and the tree-edge merge is the common way that happens rather than the
definition of when it does.

Whether the analyzer ever *builds* that shape is a separate question from whether the representation
permits it. §4.7 answers it — no, for all seven uncovered accessors — which makes the union arm
defensive rather than load-bearing, and §12.1 counts it so that stays measured.

R3 has one consequence that is easy to miss and is spelled out in §3.5: **if the id changes, the merge
must report a non-empty delta**, even when the shape did not change.

### 2.3 Concurrency

Manager operations must be thread-safe, and that follows from §2.1 rather than being an extra
requirement: putting allocation and union on the shared `TreeApManager` is what makes them
cross-thread. §3.6 gives the read/write split and what it costs.

### 2.4 The branch invariant

> **At most one manager per branch.** Along any single root-to-leaf path of a fact tree, every `[any]`
> edge belongs to the same manager. Different managers in different branches are fine; two different
> managers on one branch are impossible.

This is not a tidiness rule, it is what the bound is made of. Take `X.[any]ᴹ¹.f.[any]ᴹ²` with `f` not
covered. If `M1` and `M2` are separate pots, the outer `[any]` materialises up to `L` prefixes and each
of them carries a copy of the inner `[any]`, which materialises up to `L` more: the population under
one origin is `L²`, and with `d` nested `[any]`s on a branch it is `Lᵈ`. Unioning them makes the whole
branch spend from one pot and restores the flat `L` of §8.1. **The invariant is the difference between
a population bound and a depth-indexed one**, which is the exact failure §1.2 was rejected for.

It is also what makes several other rules expressible at all:

- **A walk down one path meets one manager.** That is why TIFA can carry a single `governingAnyId`
  through `abstractAccessPath` (§6.3) — no sets, no joins, one reference per walk state.
- **A linear chain fold needs exactly one id.** `createAbstractNodeFromReversedAp` (AT:2266) folds a
  premise chain that may contain several `[any]` links; they are all on one branch by construction, so
  one id covers the fold (§6.3).

**A tempting shortcut is to argue the invariant away, and it does not survive contact with the code.**
The argument runs: `[any].f.[any]` is impossible by construction, because the outer `[any]` absorbs
everything up to the last one, so the two edges always become one edge — and the manager union is then
just the shadow of that tree-edge merge, needing no separate rule. Half of that is right, and the half
that is wrong is pinned by a passing test.

What is right: for a **covered** `f`, `prependAnyAccessor` (AT:787-845) does collapse, `[any].[any]` is
absorbed in three places (AT:829-834, AT:886, `AccessTreeAnySuffixMatcher.kt:75-86`), and where the
collapse happens the union genuinely is the shadow of a tree-edge merge. That is the cleanest case and
§4.1 implements it exactly that way.

What is wrong: **the collapse is a property of `prependAnyAccessor`, not of construction**, and it stops
at the first accessor `[any]` does not cover.

- `stripAnyBelowCoveredPath`'s `else -> node` arm (AT:839) does not descend an uncovered accessor, so
  an `[any]` beneath one survives a prepend **by design**. `AnyAccessorCollapseTest.kt:143-153` —
  *"prepending any does not collapse an any below an uncovered accessor"* — asserts through the public
  `prependAccessor` API that `[any].{Box}.[any].$` comes out intact. `AnyAccessorPremiseTest.kt:116-144`
  pins `[any].![m].[any].$`, `[any].{Box}.[any].$` and `[any].x.{Box}.[any].$` as the *correct* results.
  TIFA:353-355 states the same in its own words: *"The reachable shapes are `[any]` under `[value]` or
  under a type-info accessor."*
- **Nothing asserts the shape is illegal.** The raw choke point `create(accessor, node)` (AT:2195-2208)
  checks taint marks and nothing else; `TreeApManager.create(...)` (AT:2221) checks nothing. A grep of
  every `check(` in AT finds no nested-`[any]` assertion. `AnyAccessorCollapseTest.kt:128` builds
  `[any].x.y.[any].$` raw, deliberately, as a test oracle.
- The raw rebuild sites of §4.1 fold premise chains straight through `create`, and premises can carry
  two `[any]` links for exactly the uncovered-accessor reason above.

So there are branches on which two `[any]` edges **legitimately coexist and never merge**, and their
managers must nevertheless be one pot — because the population under them is still multiplicative. The
invariant is a manager-level obligation in its own right, not a corollary of tree normalisation.

**One rule discharges almost all of it, and it is the rule §4.7 installs anyway.** Whenever an `[any]`
edge is *installed over a child*, normalise: collapse every `[any]` reachable through a covered-only
path into the new edge, and — for the ones under an uncovered accessor, which must not be collapsed —
union their managers without touching the tree. After that call, every `[any]` in the subtree shares
the installed edge's manager, which is the invariant, established at the only moment it can be
violated.

Because §4.7 enforces that at all three construction routes, three of the four ways a second `[any]`
lands on an occupied branch stop being separate obligations:

| # | how a second `[any]` lands on an occupied branch | discharged by |
|---|---|---|
| B1 | prepend: a new `[any]` placed **above** everything | the normalisation, which is exactly what `prependAnyAccessor` already did |
| B2 | graft: a delta rooted at `[any]` spliced **below** a receiver whose path already crosses an `[any]` | the normalisation — concat rebuilds the receiver's spine, so the outer `[any]` edge is re-installed with the grafted subtree already in place (§4.4) |
| B4 | raw reconstruction by a spine rebuild, a chain fold, or the wire | the normalisation, since all three routes go through AT:2195 / AT:2221 / AT:2018 (§4.7) |
| B3 | merge: two trees combined | **the per-position union (R3)** — not the normalisation |

An earlier draft discharged B2 by threading a `governingAnyId` down `concatToLeafAbstractNodes`'s
recursion. That is no longer needed and has been removed: the spine rebuild re-installs the edge, and
the normalisation sees the whole subtree at once. Insisting on the collapse bought the simplification.

B3 needs no extra machinery, and it is worth saying why, because it looks like it should. When receiver
and arrival meet at position `p`, an `[any]` the receiver owns *at* `p` and an `[any]` the arrival owns
*below* `p.f` are **not on the same branch** — `p → [any] → …` and `p → f → …` diverge at `p`. So the
ordinary per-position union (R3) plus recursion is complete, and the only extra source is
`trimAnyCoveredAndPushChildren` folding one side's covered `f.[any]` **into** the other's `[any]`, which
§4.2 already lists as a union site. Hoists (`limitFieldAccessCached`, `collapseElementAccess`) move
`[any]`s *up*, which can only remove same-branch pairs, never create them.

---

### 2.5 The automaton is cyclic, and the cycle is the fixed point

Take the shape the whole investigation is about — a fact `x.[any].*` — in a method containing

```
while (...) { x = x.a }
```

Start from what happens **today**, because it is more delicate than it looks. `fieldRead`
(`JIRMethodSequentFlowFunction.kt:403-444`) skips its `unchanged(factAp)` arm when `assignTo == factAp.base`,
so this emits a plain `FactToFact` sequent and the `enqueuedUnchangedEdges` hash set is never consulted.
`readAccessorTo` is `readAccessor(a)?.rebase(x)`, and `getChild(a)` on `{[any] → abstractNode}` walks its
four statements to: no literal `a` child, `anyChild` null, then the covered arm rebuilding
`create(ANY_ACCESSOR_IDX, abstractNode)`. The result is **structurally equal to the receiver and a fresh
object** — `x.[any].*` in, `x.[any].*` out, nothing grows.

So today's loop terminates on exactly one guard: `mergedAccess === currentAccess` at
`MethodEdgesInitialToFinalTreeApSet.kt:100`, which fires only because `mergeAddStep` returns **`this`**
(the receiver) rather than rebuilding — and that in turn holds only because the `[any]` child is the
shared `abstractNode` singleton, so `mergeAccessorsRaw` sees `mergedNode === thisNode` and
`trimModifiedAccessors` short-circuits. Nothing else stops it: `edgeExceedLimit` gates only delayed
initial and summary edges, never `addSequentialEdge`; the `[any]` depth charge is a constant 11 every
lap; and `filterStartsWith`'s `maxDepth` prefilter disables itself whenever an `[any]` is in reach.
**The whole loop rests on one reference comparison**, which is worth knowing before adding a field to
node identity.

Now add the manager. By R4 the read yields the residual carrying the **successor** state, so iteration 1
produces `x.[any]` with `m₁ = m.a`, iteration 2 with `m₂ = m₁.a`, and so on. The tree shape never
changes; only the id does — and the id is in identity, so without a union every lap is a new fact.

The storage merges the arrival into the accumulated fact. The two `[any]` tree edges are at the same
position, so R3 fires: `union(m, m₁)`. And `m₁` is a **successor of `m`**, so the union writes `m`'s
`a`-transition to point at the representative of `{m, m₁}`, which is `m` itself:

```
m --a--> m          a self-loop, and the automaton's language is now  a*
```

**That self-loop is what makes the loop terminate**, and with §3.5's rule it terminates on the *same*
lap: the union is performed while computing the merged id, the merged representative equals the
receiver's, the guard passes, `mergeAddStep` returns `this`, and `===` fires. Had the guard compared
stored references instead, the merge would rebuild, one extra lap would run, the read at `m` would then find the
existing `a`-transition — no mint, no charge, same id — and it would converge on lap two. Either way it
converges; comparing representatives makes it converge immediately and keeps the fact out of the
worklist.

Refusing to create the cycle — for instance by forbidding a union between a state and its own
descendant — would produce `m, m₁, m₂, …` without end. Every one of them is a *different* id, and by
§3.6 a different id is a non-empty delta, so the analysis would never converge. **The cycle is not a
defect to be engineered away; it is the design's termination argument, and any implementation that
breaks it breaks the analysis.**

What the cycle costs is stated rather than hidden: the automaton's *language* becomes infinite (`a*`),
so any measure defined as "number of accepted words" is now `∞`. §2.6 is what keeps the budget finite
in spite of that. Two further consequences:

- **The union recursion must memoise on state pairs** — `memo[(x, y)]` — which it already does (§2.2,
  mirroring `AccessNodeMergePair` at AT:1122-1132). With that memo the product construction terminates
  on cyclic inputs for the standard reason: the pair space is finite and each pair is expanded once.
  Without it, a cycle is an infinite loop.
- **Nothing may compute anything by traversing the automaton.** Not `total`, not `pathCount`, not a
  size. Every quantity is maintained incrementally at the point of change. §2.6 is written to that
  constraint.

### 2.6 The charge is the path count, not one

A state can be reached by more than one accessor sequence — that is what the union does, and it is
the whole reason the structure is an automaton rather than a trie. Suppose the origin `m` emitted `a`
and `b`, giving states `A` and `B`, and then two facts carrying `A` and `B` merged, so `union(A, B) = C`.
Emitting `c` at `C` authorises **two** sequences, `ac` and `bc`, from one transition. Counting states
or transitions would score that 1 and under-report the population by the sharing factor, compounding
with every merge — the same class of error as §1's under-counting, arriving by a different route.

So each state carries `pathCount` — how many sequences reach it — and R5 charges
`dag.total += n.pathCount` when a new transition out of `n` is created.

`pathCount` is maintained **incrementally, never by traversal** (§2.5 forbids traversal):

| event | update |
|---|---|
| mint a dag | `root.pathCount = 1` |
| new transition `n --a--> m` | `m.pathCount = n.pathCount` |
| `union(x, y) → x` | `x.pathCount = sat(x.pathCount + y.pathCount)` |

Saturating arithmetic, at `L` — past `L` the state refuses everything anyway, so the exact value stops
mattering and a ceiling removes any overflow question.

This is an approximation in **both** directions and it is worth being precise about which:

- **It over-states relative to live facts.** When `union(A, B)` happened because two *facts* merged,
  there is now one fact where there were two, so charging 2 for its next read over-counts what is
  actually live. Over-counting refuses sooner, which §8.2 shows is sound. It is a precision cost,
  taken deliberately.
- **It under-states relative to the true language.** After `union(X, Y) → Z`, states reachable only
  through `X` now have more incoming sequences, but we do not push the increase down to them — that
  would be a subtree walk on every union, and unions are frequent. The error is bounded by the sharing
  below a merge point and is the price of `O(1)`.
- **On a cycle it stays finite**, because it is never recomputed by traversal. `union(m, m₁)` in §2.5
  sets `m.pathCount = 2` even though the language is `a*`. So a loop does not kill the origin with an
  infinite charge; it makes each *subsequent distinct* accessor at that state cost 2 instead of 1. A
  soft escalation rather than a cliff — and escalating the price of unrolling in proportion to how many
  loops have folded into a state is, on reflection, the economics this problem actually has.

**Same-dag unions do not touch `total`.** There is one pot per dag and both states were already
spending from it. Only a **dag fusion** combines pots, and it does so by summing:
`total[d] = total[dx] + total[dy]`. That over-counts the sequences the two automata had in common,
which again refuses sooner, and it avoids a full product traversal on a path §12.1 is instrumented to
show is rare.

---

## 3. Representation: a state reference in the node, two pointer DSUs

The node holds one reference — `AnyUnrollState?` — and every other piece of the structure hangs off it
(§2). There are no ids to allocate, no arrays to grow, and no table mapping ids to anything.

The two alternatives considered earlier both failed for reasons worth keeping: `anySuffixMatcher` hangs
on the node *below* the `[any]` edge — overwhelmingly the `abstractNode` singleton — so widening it
would fuse every terminal `[any]` in the program into one manager before any interning; and a plain
object reference is dropped by `markInterned` (AT:1494) exactly as the matcher deliberately is, with
none of the matcher's "pure function, safe to rebuild" justification. The second objection is answered
by putting the field in identity (§3.4), which makes it a constructor parameter with no default and
therefore a compile error to omit.

### 3.1 Why a reference rather than an id

An earlier draft used a packed `(dagId, nodeId)` `Long` with columnar side tables. It was smaller per
state — 8 bytes against ~32 — and it was wrong for one reason that outweighs the rest.

- **Ids leak; references do not.** A DSU over ints keeps a slot for every id ever minted, whether or
  not it survived its first merge. That is precisely the case to worry about — mint a state, merge it
  into another, discard the node that carried it — and it is also precisely the case a reference
  recovers: the transient state becomes unreachable and the collector takes it. §3.8 is honest about
  how far that goes, which is not as far as it sounds.
- **The alternative to reclaiming was a valve, and a valve is a worse answer.** The columnar design
  needed an id-space ceiling with an overflow dag to bound the leak — sound, but it hides the failure
  instead of removing it, and a run that silently hit it produces numbers no one can interpret.
  Reclamation makes the valve unnecessary; §3.8 retires it.
- **It needs no machinery this codebase does not already have.** A `WeakReference` + `ReferenceQueue`
  drain over a registry would work, but it would be the first `ReferenceQueue` in the repo — a grep
  finds none, and `WeakReference` appears exactly twice, in `Async.kt`'s `weakLazy`. The house pattern
  is soft references parked in a `SoftReferenceManager` queue and cleared by hand from a GC
  notification (`util/SoftReferenceManager.kt`, `util/MemoryManager.kt`). Plain reachability needs
  neither.
- **The states must be strongly referenced, and that is not negotiable.** They must never be routed
  through `SoftReferenceManager`: a budget that evaporates under memory pressure is a budget that
  silently refills, which is §1's failure mode arriving through the heap.
- **Stale references are as harmless as stale ids.** A node built before a union keeps pointing at the
  merged-away state, and `find` still reaches the right representative. Nothing is chased through the
  tree.
- **A union is still a single write** — `y.parent = x` — and it rewrites no node.
- **It costs the same in the place that matters.** One compressed oop takes `AccessNode` from 56 to 64,
  identical to the `Int` or the packed `Long`.

What the reference gives up is the ability to answer "which pot?" with two array reads.
`state.find().dag.find().total` is three pointer hops instead — still constant, on a path that already
does a hash lookup for the transition.

### 3.2 The union, and the preferred root

`union(this.anyId, other.anyId)` with **`this.id` as the preferred new root** — the receiver's
representative wins. In `mergeAdd(other)` the receiver is the accumulated, long-lived tree and `other`
is the arrival, so preferring the receiver keeps ids stable on the structure that persists and lets the
transient side's id die out.

Representative choice is **semantically neutral**: the union merges the states by product (§2.2), so
the merged content is identical whichever int survives — only the name differs. That matters for
determinism. The representative depends on merge order and therefore on schedule, but nothing
observable depends on it.

It is not neutral for *speed*, and §2.5 is why. In the loop there, the accumulated fact carries `m` and
the arrival carries the successor `m₁`. Preferring the receiver makes `m` the representative, so the
stored node's id is unchanged, the merge returns `this`, and the storage's `===` guard fires on the
**same** round. Preferring the arrival would rename the stored fact, produce a delta by §3.5, and cost
an extra lap of the fixpoint for every folded loop in the program.

### 3.3 The DSU is pointer-based, and there is no DSU class

`analysis/alias/IntDisjointSets.kt` is the in-repo DSU, and an earlier draft of this design specified a
dedicated concurrent replacement for it — segmented arrays that are never copied, a lock-free `find`
with path halving, a synchronized `union(x, y, preferRoot)`. The state objects of §2 make that whole
component unnecessary: the DSU is two fields and two small functions.

```kotlin
fun AnyUnrollState.find(): AnyUnrollState {
    var cur = this
    while (true) {
        val up = cur.parent ?: return cur
        val grand = up.parent ?: return up
        cur.parent = grand          // path halving, best-effort; a lost race is harmless
        cur = grand
    }
}
```

Every property the dedicated class was written for still holds, and two problems it existed to solve
simply do not arise:

- **Path halving, not full compression**, so `find` writes at most one field per step and a racing
  writer can only install an equally valid link. `parent` is `@Volatile`; a reader that sees a stale
  link walks one hop further and converges.
- **No segmented storage, because there is no array.** The dedicated class needed segments precisely
  because copy-on-grow would let a `find` holding the old array return a superseded representative.
  With links inside the objects the invariant "parent links only ever move towards a root" is
  structural.
- **No `preferRoot` comparator problem.** `IntDisjointSets`' `RankStrategy` is a stateless
  `IntComparator` over values, which cannot express "prefer the receiver" — that is a property of the
  call, not of the two operands — and its `check(cmp != 0)` demands a total order that "prefer the
  receiver" is not. `y.parent = x` states the preference directly (§3.2).
- **No removal protocol.** `IntDisjointSets` carries `removeAll`/`prepareRemoveAll`/`RemoveResult`,
  `forEachElementInSet`, `collectElementParentPairs` and an `ImmutableIntDSU`/`mutableCopy`/`equals`
  pair, none of which this design wants. Removal is the collector's job now.

#### The concurrent write to `parent`

`parent` is written from two places — `union` repoints a root, path halving shortens a chain — and both
run on the analysis thread pool. The interesting failure is not a lost update; it is a **cycle in the
DSU forest**, and a cycle makes `find` spin forever:

```
thread A:  union(x, y)   ->  find(x)=a, find(y)=b,  b.parent = a
thread B:  union(y, x)   ->  find(y)=b, find(x)=a,  a.parent = b     // interleaved
```

Both threads saw two distinct roots, both wrote, and now `a.parent == b` and `b.parent == a`. Nothing
detects it and the next `find` hangs. This is the reason the rule is not "make `parent` volatile and
hope":

> **`find` and the parent write must be inside the same critical section for a union.** Unions are
> serialized on one `TreeApManager` lock; a root discovered under that lock is still a root when it is
> written.

With that, the two writers have **disjoint write sets**, which is what lets halving stay lock-free:

- **`union` writes only to roots** — it writes `b.parent` where `b` was `find(y)`, i.e. `b.parent` was
  `null`, established under the lock.
- **Path halving writes only to non-roots whose parent is also a non-root** — the loop writes
  `cur.parent = grand` only after reading a non-null `cur.parent` *and* a non-null `up.parent`.

So halving never touches a root and `union` never touches a non-root. Four further properties make the
lock-free half safe rather than merely convenient:

- **A halving write can only shorten a valid path.** `grand` was an ancestor of `cur` when it was read,
  and ancestors are permanent: a root may acquire a parent, but a non-root never leaves its tree. So
  the link installed is always still valid, even if it has since stopped being the root.
- **A lost halving write is harmless.** Two threads racing to halve the same node write links that are
  both valid; whichever lands, `find` still converges. Plain volatile writes are enough — no CAS.
- **A stale read costs a hop, not a wrong answer.** `parent` is `@Volatile`, and a reader that misses a
  recent union simply walks further up and reaches the same root.
- **Any decision that mutates must re-`find` under the lock.** A lock-free `find` on the fast path is a
  hint; the union, the record and the charge all re-resolve inside the critical section. This is the
  one rule that turns "reads are stale" from a correctness problem into a performance note.

`pathCount` is read on the charge path and written by `union`, so it follows the same discipline: the
budget test, the transition insert and the `total` increment happen **together** under the lock (§2.6),
or two concurrent unions read the same pre-merge counts and one increment is lost.

That leaves the hot path lock-free, which is the point of the split: the common case for R4 is *the
transition already exists*, answered by a `ConcurrentReadSafeInt2ObjectMap` lookup
(`util/ConcurrentReadSafeInt2ObjectMap.java`, the house capture-and-retry type, already used for
`AccessBasedStorage.children`) with no lock and no allocation. The lock is taken only when a transition
must be **created** or two states **merged** — the first is bounded by `L` per dag (§3.8), the second by
the union count. Both are rare against the number of reads, which is the whole reason the automaton
exists.

Dags get exactly the same treatment: `AnyUnrollDag.parent` volatile, the same `find`, `total` written
under the same lock. And note the two-layer union (§2.2) must take the lock **once** for the whole
operation — fusing dags and then merging states are not two independently-locked steps, or a third
thread can observe a dag fused with its states not yet merged.

### 3.4 Identity, and why the sentinel matters

**`anyId` participates in node identity** — `hash`, `equals`, and `AccessTreeInterner.InternStrategy`.
Without that, interning fuses structurally identical `[any]` subtrees across unrelated facts in
unrelated methods (`InternStrategy` compares children by identity and nothing else), and since the
carrier of every terminal `[any]` has the same shape, the budget would collapse into one global pot.

The node-level invariant that makes this tractable:

> **`anyId != 0L` if and only if the node owns an `[any]` edge.**

It should be a `check()` in the constructor's init block. Everything below follows from it, and it
turns the whole propagation problem into a mechanical rule (§3.7).

**The pressure to relax it, and why the relaxation belongs somewhere else.** The strict form makes
`prepend(clear(X, [any]), [any])` mint: reading or clearing the `[any]` accessor and then prepending
one back is a round trip that should be free, and under a naive reading every lap of it burns a fresh
origin — §8.5's churn, and via §3.8 a direct memory cost. The obvious fix is a **dormant** id: let a
node with no `[any]` edge carry the id of the one that was just taken off it, and let
`prependAnyAccessor` find it again instead of minting.

Putting dormancy on `AccessNode` is the wrong place for it, and a census of the round trips says so
twice over.

**First, almost nothing needs it.** Every explicit read or clear of the `[any]` accessor in the repo
was enumerated, and the read-then-prepend round trips are:

| site | round trip | already covered by |
|---|---|---|
| `getChild` AT:531 → AT:539 | clear-repeat then re-prepend | **co-located** — the id flows directly (§4.5) |
| `reconstructRemainder` AT:711 → AT:721 | clear then re-create | **co-located** within one function (§4.1) |
| `TIFA:227` → `TIFA:262` | read, then `[any]` re-attached to the *premise* prefix | §6.3's `governingAnyId` in the walk state |
| `AccessPath.kt:368` → `:372` | `[any]` recorded on the matched prefix | premise side, no manager (§6) |
| `AccessBasedStorage.kt:144` | premise `[any]` consumes the fact's, documented at `:117-120` | not re-prepended by design |
| `Cleaner.kt:181` → `:185` and `:209` → `:214` | **genuine cross-operation round trip** | nothing — this is the real case |

One file. `abstractOnly` (`JIRMethodSequentFlowFunction.kt:594`) erases the `[any]` and never restores
it, so it needs nothing either.

**Second, `Cleaner`'s round trip never touches a bare node.** `readAccessor(AnyAccessor)`,
`clearAccessor(head)` and `prependAccessor(AnyAccessor)` are all `FinalFactAp` operations — they run on
the **`AccessTree` wrapper**, which is thin, **not interned**, and not part of node identity. So carry
the dormant id there:

> **Dormancy lives on the `AccessTree` / `AccessPath` wrapper and on walk-local state, never on
> `AccessNode`.**

That buys everything the node-level version would have, and avoids all of its costs:

- **Zero bytes on the node**, zero interner fragmentation, and no second identity axis.
- **It cannot break the convergence guard.** §2.5's fixed point depends on `mergeAddStep` returning
  the *receiver object*, which in turn depends on the `[any]` child still being the shared
  `abstractNode` singleton so that `mergeAccessorsRaw` sees `mergedNode === thisNode`. A dormant id in
  node identity would make `abstractNode` and `abstractNode(dormant = X)` distinct objects, the merge
  would rebuild, `===` would fail, and every loop in the program would cost extra laps. This is a real
  trap and the wrapper sidesteps it entirely.
- **`createElementAndField` (AT:2243) needs no change.** It collapses childless, exclusion-free results
  onto the shared singleton, which would have erased a node-level dormant id in exactly the common case
  — `getChild(ANY_ACCESSOR_IDX)` on `x.[any].*` returns `abstractNode`.
- **`isLegalNodeBelowTaintMark` (AT:488-489) stays as it is.** It is the only structural `==` against a
  singleton in the repo, and if a dormant leaf failed it, `addParent` (AT:728) would throw
  `"Impossible accessor"` on every taint-mark prepend — a hard crash, not a silent loss.
- **It is transient by construction, which is correct.** Storages hold bare nodes, so a wrapper-carried
  id cannot leak into persistent state. Dormancy is a within-operation notion and this makes it one.

`rebase` (AT:50) must carry it, since it rewraps the same node under a new base.

Four things make identity participation safe here, where it was not for the superseded per-fact limit:

- **`[any]`-free nodes carry `null`**, contribute nothing to `hash`, and compare exactly as
  today. That is the overwhelming majority of nodes, so **the feature is provably inert on trees with
  no `[any]` in them** — and with `L < 0` every node is `0`, making the analysis bit-identical to today.
- **The taint-mark check is untouched, and now provably.** `isLegalNodeBelowTaintMark` (AT:488-489)
  compares structurally (`==`, not `===`) against three singletons. A node with `anyId != null` owns an
  `[any]` edge, hence has non-null `accessors`, hence fails `isStructurelessLeaf` and was never equal
  to a singleton anyway; and the singletons keep id `0`. So no comparison outcome changes. This is
  precisely the trap that killed identity participation for the superseded per-fact limit, where the
  limit rode on *every* node including the leaves.
- **`createElementAndField`'s singleton collapse stays valid.** AT:2251-2252 returns the shared `base`
  singleton whenever there are no accessors and no exclusion; by the invariant such a node has
  `anyId == null`, so the collapse never loses a state. (This is also the reason not to invent "dormant"
  ids on `[any]`-less nodes: they would break this collapse and leak into every leaf.)
- **Omissions become compile errors.** In identity means a constructor parameter with no default, so
  all five private-constructor sites — `markInterned` (AT:1494) and `Serializer.readAccessNode`
  (AT:2018) included — must supply it.

**`equals` compares the stored reference with `===`, and `hash` mixes in `anyId.id`, never `find`.** A `hashCode` that
called `find` would *change over time*: a union moves the representative, the node's hash changes, and
every hash structure already holding it — `AccessTreeInterner`'s bucket map, `EdgeSet`
(`EdgeCollection.kt:177`), `hashSetOf<FinalFactAp>()` in `MethodAnalyzerEdges.kt:47` — silently loses
it. `equals` must match `hashCode`, so it too compares raw. `find` appears only in the merge guard
(§3.5), where it decides whether to rebuild rather than what a node *is*.

Do canonicalise at construction — pass `state.find()` in, so freshly built nodes point at
representatives, the structural duplicates a union leaves behind die out as the analysis rebuilds trees
(§4.3 shows it does constantly), and the merged-away states they were the last holders of become
garbage (§3.8). The distinction is: `find` at *build* time, the stored reference at *compare* time.

`AnyUnrollState.id` is a dense `Int` from an `AtomicInteger`, not `System.identityHashCode`, for two
reasons: it distributes better inside a hash that is already a sum of children (AT:351-384), and it
keeps `AccessNode.hash` no less reproducible than the rest of the analysis — an identity hash would
add a fresh source of run-to-run variation to §8.4's list.

Three places must learn about the id, not one:

- `AccessNode.hash` (AT:351-384) — mix it in additively; nothing decodes `hash`, it is a bucket key
  plus an equality prefilter, so no bit surgery is needed.
- `AccessNode.equals` (AT:408-422).
- **`AccessTreeInterner.InternStrategy.equals` (`AccessTreeInterner.kt:15-29`)** — easy to miss,
  because it is a *different* comparison from `AccessNode.equals` and already diverges from it: it
  omits `deepAccessorExclusion` and relies on `hash` alone to separate those. Relying on the same
  trick for `anyId` would fuse two managers on a hash collision, silently merging two budgets. Compare
  it explicitly.

Cost: one `Int` takes `AccessNode` from 53 bytes of content / 56 aligned to 57 / **64**. That +8 is
what §12.7 gates on. Note the second int a subtree summary would have wanted is *free* at that
alignment (61 → 64) — but §4.1 shows it is not needed, because `prependAnyAccessor`'s slow arm already
walks the subtree and can accumulate the union as it goes.

### 3.5 A union produces no delta — and the union must happen anyway

An earlier draft had the opposite rule: an id change makes the merge report a non-empty delta, so the
fixpoint sees that a union may have pushed `total` over `L`. Tracing the actual guard shows that rule
is both **vacuous and unwanted**, and that the correct rule is stronger and cheaper.

The merge guards must compare ids by **representative**, not raw:

```kotlin
// AT:1158-1165 mergeAddStep, and AT:1212-1218 mergeAddDeltaStep -- both gain the id term
val mergedAnyId = union(this.anyId, other.anyId)          // SIDE EFFECT -- see below
if (isAbstract == this.isAbstract && isFinal == this.isFinal
    && deepExclusions == this.deepAccessorExclusion && mergedAccessors == null
    && sameRepresentative(mergedAnyId, this.anyId)) return this
```

**Under receiver-preferred unions (§3.2) that term can never fire.** `union(x, y, prefer = x)` returns
`find(x)`, and `this.anyId` is `x`, so the merged representative *is* the receiver's representative by
construction. The term is a safety net for the day someone changes the preference rule, not a mechanism.

That is the right outcome, and the earlier draft's justification for wanting a delta does not hold:

- **A tightened budget needs no re-propagation.** Refusal is evaluated at *read* time. A fact that is
  not re-propagated is not re-read, so there is nothing to revisit. And the results already produced
  under the laxer budget were produced with *less* coarsening, i.e. they are more precise and still
  sound (§8.2) — a budget that tightens afterwards cannot retroactively make them wrong.
- **Rewriting ids to chase representatives is not worth a delta either.** `find` is path-halved and
  effectively constant; letting a stored node keep a stale reference costs nothing on the hot path, while
  reporting a delta for it would re-propagate a fact whose value did not change. The earlier draft had
  this backwards.

So the rule is: **no delta for a union.** That removes the churn amplification the earlier draft
introduced, and with it the fixpoint-inflation risk it created.

**The trap, and it is a serious one: the union is a side effect that must happen even when the guard
returns `this`.** The guard is evaluated *after* the merged id is computed, so the union has already
run — but an implementation that "optimises" by testing the shape first and returning `this` before
unioning would skip it. Then §2.5's self-loop never forms, every lap of every loop produces a fresh
successor id, and **the analysis does not terminate**. Order the code so the union cannot be skipped,
and let the §12.1 cycle test pin it.

The two identity fast paths above the guard — `if (this === other)` at AT:1237 and `if (a === b)` at
AT:1249-1253 — need no change and must not get one. The same object trivially has the same id, so the
union would be a no-op and returning it with a null delta is right.

### 3.6 Threading

Manager operations are cross-thread because `TreeApManager` is created once per phase and shared by
every unit runner on a pool of `(availableProcessors() / 2)` threads
(`TaintAnalysisUnitRunnerManager.kt:91-96`). Everything mutable already on it is explicitly safe —
`AccessorInterner` uses `synchronized(this)`, `SoftReferenceManager` uses `ConcurrentLinkedQueue` plus
`AtomicBoolean`.

The split that matters for cost: **`find` lock-free on the hot path; `union` and automaton mutation
synchronized and rare.** §3.3 works through why that is safe rather than merely fast — the two writers
have disjoint write sets, and the failure a naive version invites is a cycle in the DSU forest, which
hangs. This is not what a narrower design would have needed — the two spend sites are
individually single-threaded (TIFA is one per `NormalMethodAnalyzer` with all-plain-fastutil fields;
the subscription storages are touched only by the owning caller runner). It is putting id handling on
the shared manager that makes it cross-thread, the deliberate trade for a budget that is genuinely
shared rather than partitioned 7,347 ways (§1.1b).

### 3.7 The propagation rule, stated mechanically

The census of AT (2,294 lines) finds **five private-constructor call sites and roughly twenty
`manager.create(...)` sites** that produce a node from an accessor array. Enumerating them as prose
would not survive the next refactor. The invariant above turns it into one rule that a reviewer can
check locally at each site:

> Every construction passes an explicit `anyId`, and it must satisfy
> `anyId != null  ⟺  ANY_ACCESSOR_IDX ∈ accessors`.

Which value, by what the site does to the `[any]` edge:

| the site… | passes |
|---|---|
| keeps the receiver's accessor array (`removeAbstraction`, `filter`, `updateDeepExclusion`, `markInterned`, `clearChild(non-any)`, `abstractOnly`ᐟ) | `this.anyId` |
| deletes the `[any]` edge (`removeSingleAccessor(ANY)`, `clearAllAccessorOccurrences(ANY)`, `filter` excluding `[any]`, `abstractOnly`, `AnySuffixMatcher.getNonMatchingNode` when it trims the edge) | `0` |
| merges two nodes (`mergeAddStep` AT:1170, `mergeAddDeltaStep` AT:1228, `bulkMergeAddAccessors` AT:1119) | `union(this.anyId, other.anyId)` when both own an `[any]`; the non-zero one when only one does; `0` when neither |
| builds the **delta** node (`mergeAddDeltaStep` AT:1220) | the same representative — the delta is what propagates, so an id-less delta would strand the manager at the far end |
| creates a new `[any]` edge | see §4.1 |

ᐟ`abstractOnly` (AT:1043) drops *all* children, so it passes `0`; it is listed on both rows because
the naive reading — "it keeps the exclusion, so keep the id" — is wrong.

The one awkward site is `bulkMergeAddAccessors` (AT:1092), which takes a
`List<IntObjectImmutablePair<AccessNode>>` of `(accessor, child)` pairs and can therefore **attach an
`[any]` edge to a parent that has none** — with no access to the id of the parent the edge came from.
Two facts make it tractable: only `concatToLeafAbstractNodes`'s own child loop (AT:1688-1691) ever puts
an `ANY_ACCESSOR_IDX` entry into such a list, and at that point the source parent is the loop's
receiver, so `this.anyId` is in scope. `addParentFieldAccess` (AT:948) and `limitFieldAccessCached`
extract entries keyed by a *field* accessor only. So the entry type gains an id field that is
meaningful for the `[any]` entry alone, and the assertion above catches any future caller that forgets
it.

### 3.8 Memory: the live set, and why there is no valve

Because states are ordinary objects reached only from live facts, the cost is the **live** automaton,
not the history of everything ever minted:

| thing | cost |
|---|---|
| one live state | 12 B header + `id` + `dag` + `parent` + `pathCount` + `children` = 32 B |
| one live transition | one `Int2ObjectOpenHashMap` slot, plus ~48 B for the map on the first transition out of a state |
| one live dag | 12 B header + `id` + `parent` + `total` + root ref = 32 B |
| every `AccessNode` | +4 B for the reference, which rounds to +8 (§2) |

The live set is bounded by the budget itself: a new transition always charges at least 1
(`pathCount ≥ 1`, §2.6) and the pot stops at `L`, so **an automaton has at most `L` transitions and
therefore at most `L + 1` states**. So

```
live bytes  ≈  live origins × (L + 1) × ~48
```

and the crucial word is **live**. The columnar alternative was 8 bytes per state but per state *ever
minted*, monotonically for the whole phase. Which wins depends on the surviving fraction: objects win
below roughly 1 in 6, arrays win above it.

**Be precise about what reclamation actually recovers, because it is narrower than "dead automata are
collected".** An `AccessNode` being alive is a poor proxy for the fact still mattering: every storage
in the engine is merge-monotone and never deletes (`TreeSetWithCompression.edges` is a fixed array of
ever-growing trees; `MergingTreeSummaryStorage.edges` is never nulled; `MethodSameBaseInitialFact.added`
only ever grows), and interning makes liveness non-local — a node survives because some unrelated
method's summary happens to share its shape. The only bulk reclamation is the wholesale
`resetApManager` at a phase boundary.

So the states that reach a stored fact live for the phase, and *should* — their budgets are still being
spent from. What reclamation recovers is the **transient mint**: a state minted by
`prependAnyAccessor`, carried by a node that is immediately merged into a stored one, and then
discarded. That node dies, the state dies with it, and under the columnar scheme its slot would have
survived the phase. It is exactly the case worth fixing and it is not the whole population.

The other half of the argument is the one that does not depend on the surviving fraction: the array
version has **no upper bound at all** on a long phase, while this one is bounded by what the analysis is
still holding. And the failure mode of the unbounded version is not an abstraction — `MemoryManager`
stops the analysis at 90 % heap (`TaintAnalysisUnitRunnerManager.kt:113-118, 644`), which is the
`rc=253` these workloads already produce.

**The valve is retired.** The columnar design needed an id-space ceiling and a shared overflow dag to
stop the leak from being unbounded. That was a way of surviving a leak rather than not having one, and
a run that silently hit it would have made every other number in §12 uninterpretable. With reclamation
there is nothing to cap. If the live set is too large, the facts that keep it alive are too large too,
and the manager is not the marginal cause.

**Nothing needs a registry of states.** This was checked rather than assumed, because a registry is the
one thing that would force weak references back in: every counter in the engine is accumulated eagerly
into `MethodStats` (`UnitRunnerStats.kt`) and aggregated by *method*, and no code path iterates facts
or nodes for statistics — `countNodes` (AT:424) exists but is called from nowhere in `src/main`. §12's
counters are all increment-at-the-event, so they need no enumeration either.

**Reclamation removes the leak; it does not fix the bound**, and the two must not be confused. At cap 0
on the conductor witness the prepend sites that can mint are `addParent/alias` 33,578,
`addParent/source` 6,058 and `addParent/fieldWrite` 662 — call it **40k** mints. (`abstractionFact`
3,603 and `identitySummary` 404 are made to inherit or to heal on first graft by §6.3 and §4.4;
`addParent/?` 1,062,285 is `getChild`'s own re-prepend, which reuses under R4; `concat` 1,170,752 is
propagation, not creation.) If those 40k stayed distinct and live, `L = 100` would mean a 4M population
bound — **worse than the 735k for which §1.1b rejected the per-context counter** — and about 190 MB of
live automata. That is not a memory budget to plan for; it is the number §12.1 has to show collapsing
toward the handful of real `[any]` origins the witness has.

Three things in this design attack it directly, and all three exist for other reasons: **§4.7's forced
collapse**, which turns every nested-`[any]` normalisation into a union; **§6.3's inheritance**, which
stops the abstraction minting per emitted premise; and **§3.4's dormancy on the wrapper**, which makes
a read-then-prepend round trip reuse rather than mint.

---

## 4. The `[any]` lifecycle map

Every site where an `[any]` edge is created, absorbed, propagated or read, with its manager rule. A
missed row is not a crash — it is a silent budget refill, which is the failure mode of §1.

### 4.1 Creation — every site that writes an `ANY_ACCESSOR_IDX` edge

An earlier draft of this table listed five sites and called three of them "no predecessor exists". A
full census of AT found **seven**, and two of the three "no predecessor" claims were wrong. The
corrected table:

| site | what happens | rule |
|---|---|---|
| AT:788 `prependAnyAccessor` fast arm | `create(ANY_ACCESSOR_IDX, this)`, guarded by `!containsAnyInThisOrDeepNodes` | **mint** — the only unconditional mint in the engine |
| AT:807 `prependAnyAccessor` slow arm | one new `[any]` that has **absorbed N pre-existing ones** | **union the N**, never mint (§2.4 B1) |
| **AT:1750 `filterStartsWith` spine rebuild** | `parentAccessors.foldRight(node, ::create)` re-creates every walked edge **raw**, `[any]` included | **carry the id of the `[any]` that `getChild` consumed at that step** |
| **AT:721 `reconstructRemainder`** | `create(accessor, it)` raw, on the path `splitOnMatching` matched; live at MIFAS:230 | same — carry the consumed edge's id |
| AT:1119 `bulkMergeAddAccessors` | can attach an `[any]` entry to a parent that owns none | id travels with the entry (§3.7) |
| AT:2266 / AT:2276 `createAbstractNodeFrom{ReversedAp,Accessors}` | fold a **linear chain** through raw `create`; live at TIFA:100 and MIFAS:155 | **one id for the whole fold**, inherited where available (§6.3) |
| AT:2018 `Serializer.readAccessNode` | an `[any]` arrives from the wire | mint, one per tree, threaded down (§9) |

Two of these are new and both are load-bearing.

**AT:1750 is the single largest read channel in the engine.** `filterStartsWith` walks a premise with
`getChild` — which consumes each `[any]` it passes — and then rebuilds the spine over the surviving
leaf with the *raw* `create`, bypassing `prependAnyAccessor` entirely. At cap 0 on the conductor
witness this site is 657,633 events, all `fromAny`. Minting there would refill the budget on every
subscription match; treating it as a pure rebuild and dropping the id would strand every manager at
the first storage hop. The walk is linear, so the fix is small: record the consumed id alongside each
entry of `parentAccessors` and use it when the folded accessor is `ANY_ACCESSOR_IDX`.

**The union inside the collapse is not complete as stated, and the gap is the uncovered accessor.**
`stripAnyBelowCoveredPath` (AT:817-845) hoists `[any]`s found on *covered-only* paths; its
`else -> node` arm leaves a subtree under an **uncovered** accessor untouched and does not descend it.
A type-info accessor is uncovered and, unlike a taint mark, may legitimately carry children — so
`T.[typeinfo].[any]ᴹ²` survives the strip (and must: `AnyAccessorCollapseTest.kt:143-153` asserts it),
and the new `[any]ᴹ¹` lands above it. Two managers on one branch, §2.4 violated, with no collapse to
carry the union.

So `collapseNestedAny` does two things, not one: **collapse where legal, union where not.** In the
`else` arm, when the child has `containsAnyInThisOrDeepNodes`, scan it and union the managers found
without touching the tree. Gated on the existing flag this costs nothing in the common case, and the
walk is already there — which is also why **B1 needs no new node field**: the slow arm accumulates the
N-way union as it goes, and the fast arm's `!containsAnyInThisOrDeepNodes` guard is already the O(1)
case split.

Because §4.7 calls `collapseNestedAny` at every site that installs an `[any]` edge, that one function
is what makes the whole §2.4 invariant hold: after it returns, every `[any]` in the subtree is either
gone or shares the installed edge's manager.

### 4.2 Absorption and destruction

| site | what happens | rule |
|---|---|---|
| AT:817 `stripAnyBelowCoveredPath` | deletes **every** `[any]` reachable through a covered-only path and hoists their subtrees under one new `[any]` | **N-way union**, N unbounded — see §4.5 |
| AT:876 `absorbCoveredByAnyPrefix` | fixpoint loop; consumes an unbounded number of the delta's `[any]` edges into the receiver's | union consumed into receiver's; charge the absorbed steps |
| AT:1291 `trimAnyCoveredAndPushChildren` + ASM:124 `getNonMatchingNode` | one side's `[any]` deletes from the other everything its suffix language denotes; **runs on every `mergeAdd`** with `foldToAny = true` (the default) | **union b's into a's**, both directions |
| AT:1145 / AT:1178 `mergeAddStep` / `mergeAddDeltaStep` | two `[any]` edges at one position become one | **union** (R3) |
| AT:1883 `removeAllAccessorChains` (summary compression, MTS:66) | `[any]` is an ordinary vertex of the accessor graph, so `[any]` chains collapse like any other, to a fixpoint | **union along each collapsed chain** |
| AT:952 `clearChild(ANY_ACCESSOR_IDX)` | deletes the edge and its subtree outright, **no hoist**; live at `Cleaner.kt:187` | **record lost, no refund** — see §4.6 |
| AT:1043 `abstractOnly` | destroys every child edge including `[any]` | **record lost, no refund** |
| TIFA:228 | consumes the edge, re-names it symbolically at TIFA:262 | reuse |

### 4.3 Propagation

`markInterned` (AT:1494) passes `accessors`/`accessorNodes` **by reference**, so `[any]` edges survive
verbatim — but it deliberately does not copy `anySuffixMatcher`, and **a manager field would be
dropped by the same code path**. `transformAccessors` (AT:1846) never rewrites accessor keys, so the
~10 operations built on it (`filterAccessNode`, `limitElementAccess`, `annotateAbstractNodes`,
`clearAllAccessorOccurrences`, `limitFieldAccessCached`, `internNodes`, …) all preserve `[any]` keys
and need only carry the manager.

Two propagation sites move an `[any]` **up** an arbitrary number of levels while keeping its key:
`limitFieldAccessCached` (AT:1853) hoists subtrees, and `collapseElementAccess` (AT:928) does the same
for element runs. The manager travels with the edge, so depth changes are harmless — which is a point
in favour of keying the budget on the origin rather than on depth.

### 4.4 The graft — and the proof that it needs no charge

`concat` (AT:212 → AT:1433 → AT:1641). Receiver = the callee summary's exit fact mapped into the
caller; delta = the residual of the **caller's** fact below the summary premise
(`MethodCallSummaryHandler.kt:115-117`).

**The `[any]` can come from either operand, and the delta is the more common source.** With
`parentEdgeIsAny == false` — an abstract leaf under a *concrete* parent edge — absorption is skipped
(AT:1662) and the delta's node is grafted verbatim by `mergeAdd`, so a delta rooted at `[any]` lands
as `<receiver's concrete prefix>.[any]`. That is the `fromNothing` population of §1.3, and at cap 0 it
is **1,170,752 events, the single largest channel**.

But it needs **propagation, not a charge**, and this is now proven rather than argued:

> **`concat` cannot produce an `[any]` where neither operand had one.** Every transformation on the
> path is key-preserving or key-deleting — `filterTypes`/`filterAccessNode`/`transformAccessors` never
> rewrite a key; `absorbCoveredByAnyPrefix`, `limitElementAccess`, `filterDeepExclusion`,
> `limitFieldAccess`, `bulkMergeAddAccessors` and `mergeAdd` only delete, hoist or union existing
> keys; and `manager.create` at AT:1699 builds with `accessors = null`, the spine's children coming
> back only through `bulkMergeAddAccessors` from the receiver's own edge set. Every
> `[any]`-manufacturing site is a call to the raw `create(ANY_ACCESSOR_IDX, …)`, and §4.1's census
> places all of them — AT:788, AT:807, AT:721, AT:1750, AT:2271, AT:2282, AT:2018 — outside any
> concat path.

So no accessor is invented at a graft. What the graft does is *place* an existing `[any]` under a
concrete prefix the callee legitimately derived. The two rules:

- `parentEdgeIsAny == true` → the delta's covered prefix is eaten by the receiver's `[any]`: **union
  the delta's consumed managers into the receiver's**, and charge the absorbed steps to it.
- `parentEdgeIsAny == false` → **carry the delta's manager across; do not allocate.** This is the
  most-executed graft in the engine (the code says so at AT:1653-1655), so getting it wrong resets the
  budget once per summary application. It is the single largest refill hole in the design.

**But `parentEdgeIsAny == false` does not mean "no `[any]` above".** It is a *one-level* memory: the
recursion at AT:1688-1691 sets it to `accessor == ANY_ACCESSOR_IDX` for the immediate edge and forgets
everything higher. A receiver `x.[any]ᴹ¹.f.*` grafts a delta `[any]ᴹ².g` at an abstract leaf whose
parent edge is the concrete `f`, producing `x.[any]ᴹ¹.f.[any]ᴹ².g` — two managers, one branch. There is
a second, subtler route to the same shape that the census turned up: `limitFieldAccess` (AT:1676) hoists
the delta's `f`-subtree out from arbitrary depth and AT:1700 installs it under the conclusion's `[any]`,
so even a delta that was *not* rooted at `[any]` can put one there.

**§4.7's forced collapse handles both, and this is where insisting on it pays off.** `concat` rebuilds
the receiver's spine from a singleton (AT:1699) and re-adds every child through
`bulkMergeAddAccessors`, so the outer `[any]` edge is **re-installed** with the grafted subtree already
underneath it. The normalisation therefore sees `[any] → (f → [any] → g)` at install time, collapses it
to `[any] → g` for covered `f`, and unions the two managers as part of that collapse. For an uncovered
intervening accessor it unions without collapsing. Either way the branch invariant holds when the node
is built.

An earlier draft threaded a `governingAnyId` parameter down `concatToLeafAbstractNodes`'s recursion to
achieve the same thing. That is removed: it was doing at every frame what the normalisation does once,
at the point the edge is installed.

The normalisation does more than repair the invariant, and the extra job is what makes another site
affordable. Several places mint a *structurally derived* fact whose `[any]` has no predecessor to
inherit from — most sharply `SummariesIdStorageNode.finalAccess`
(`MethodInitialToFinalApSummaries.kt:151-157`), which rebuilds the identity summary's exit fact from
the storage **trie key**, a premise chain that carries no manager at all. Minted in isolation such a
fact would carry a full fresh budget. But it is never *read* before it is applied, and applying it is
exactly a graft: the caller's fact supplies the delta, the re-installed `[any]` edge unions the
caller's real manager into the fresh one, and a fresh dag has `total = 0`, so the fused pot is
`0 + total(A)` and **no budget is refilled**. The mint is transient by construction.

That is why §4.7 is ranked ahead of §6.3 in the implementation order: get the normalisation right and
the derived-fact mints heal themselves; get it wrong and they are permanent refills sitting on top of
a broken invariant.

### 4.5 The read — reuse, never allocate

Confirmed against AT:526-544: **every covered read destroys one `[any]` edge and builds a new `[any]`
node object.** The result is

```
create(ANY_ACCESSOR_IDX, anyAccessorNode.clearChild(accessor))
```

— the *same logical `[any]`* with one covered step consumed. Therefore:

- **Reuse the receiver's manager. Never allocate here.** `getChild` sits under ten callers; if a read
  allocated, the budget would be refilled on every hop and would be effectively infinite.
- **Record the consumed accessor** — that read is exactly one concrete accessor materialised out of
  this `[any]` (R4), and the fresh `[any]` node takes the **child** manager.

Three further merges happen inside the same call and all need union rules: `mergeAddMaybeNull` at
AT:535 and twice at AT:541 — and note the argument-order swap at AT:518-524 (`r.mergeAdd(l)`), and
that both run with `foldToAny = true`, so the §4.2 trimming fires **inside a read**.

Two edge cases: `addParentIfPossible` returns `null` when `containsStatic` (AT:547), so the expansion
arm can contribute nothing; and if the `[any]`'s subtree held only `accessor`, AT:807 wraps
`manager.emptyNode` — an `[any]` over nothing, whose manager still transfers.

### 4.6 The four hazards this map exposes

1. **N-to-1 unions are unbounded** at three sites — `stripAnyBelowCoveredPath`,
   `absorbCoveredByAnyPrefix`'s fixpoint, and `removeAllAccessorChains`. Worse, the trimming of §4.2
   fires *during* `stripAnyBelowCoveredPath`'s own merge loop, so **accounting must be done on the
   completed union, not incrementally inside it**.
2. **Two sites destroy an `[any]` with no successor and no refund**: `clearChild(ANY_ACCESSOR_IDX)`
   (live in the cleaner) and `abstractOnly`. Records are lost. That is sound — losing records only
   makes the remaining budget go further, i.e. less coarsening — but it means the automaton is a
   *lower bound* on what was materialised, and §12's counters must not treat it as exact.
3. **Deserialisation is the one `[any]` that can enter a prescan-phase tree** (AT:2018 never consults
   the strategy). Since prescan installs `AnyAccessorDisabled`, whose `unrollAccessor` **throws**, a
   covered read on such a tree is a crash, not a refill. §13 R8.
4. **`FilteredNode.create` interns the delta with a *fresh* interner per `concat` call** (AT:1603).
   Two structurally identical `[any]` subtrees inside one delta become one object, and the surrounding
   caches are all `IdentityHashMap`s over those interned nodes. Any identity-keyed side table
   inherits this aliasing.

### 4.7 Forcing the nested-`[any]` collapse

`prependAnyAccessor` (AT:787-808) already normalises `[any] . <covered chain> . [any]` down to a single
`[any]`. The problem is that it is the *only* thing that does: the collapse is a property of that one
function, not of construction, so every other route — the raw spine rebuilds, the chain folds, the
graft, the wire — preserves the shape. **This design forces the normalisation at construction instead.**

Two things make it worth doing beyond tidiness. Each collapse is a **union**, so forcing it directly
attacks the origin count that §3.8 and R23 turn on. And it discharges most of §2.4's B2: where the
collapse fires, two `[any]` edges become one edge and the manager rule falls out of the tree rule
instead of having to be threaded separately.

**The precondition is `f ∈ Σ`** — the collapse is `Σ* ⊇ Σ*·f·Σ*`, and §8.2 shows it fails outright for
an accessor outside `Σ` rather than merely losing precision. Three existing tests are the fence, and
each fails for a different over-reach:

| relaxation | what breaks |
|---|---|
| dropping *covered-only* on the intervening chain | `AnyAccessorCollapseTest.kt:143-153` — `[any].{Box}.[any].$` must survive a prepend, and `AnyAccessorPremiseTest.kt:139-143` pins `[any].x.{Box}.[any].$` on the premise side. A type-info accessor is not covered, so `[any]` does not range over it and collapsing would **lose** paths |
| treating an abstract leaf `.*` as a collapsible tail | `AnyFieldMarkExclusionTest.kt:317-334` — `[any].f.*` must **not** become `[any].*`, or absorption fires under C4 and the mark lands on a disjoint path. `.*` is existential, `[any]` is universal (AT:1631-1639); the licence does not transfer |
| making it a `check` on the raw `create` choke point instead of a rewrite | `AnyAccessorCollapseTest.kt:128` and `:175` deliberately build un-normalised shapes through `manager.create` as test oracles, with the helper documented as *"Raw node construction, bypassing `AccessTree.prependAccessor` so illegal shapes stay illegal"*. A `check` makes those fixtures unconstructible |

So: **a rewrite, not an assertion; the tail must be a literal `[any]` edge; the chain between must be
covered-only.** Exactly `prependAnyAccessor`'s existing predicate, applied in more places.

#### Who actually produces the shape

Two lemmas decide the whole census, and they are worth stating because they make the answer checkable
rather than enumerable:

- **L1 — union.** If an operation's result path-set is contained in the union of its operands'
  path-sets *at the same accessor positions*, it cannot introduce the infix. This covers `mergeAddStep`,
  `mergeAddDeltaStep` (both outputs — `onOtherNode` copies the other side's subtree under the other
  side's accessor), `mergeAccessorsRaw`, and `trimAnyCoveredAndPushChildren`, whose
  `getNonMatchingNode` only ever *drops* branches and rebuilds under the same accessors.
- **L2 — edge deletion.** Deleting an edge and hoisting its child preserves cleanliness **iff the
  deleted accessor is `[any]` or covered**. Deleting an *uncovered* accessor can create the infix:
  `[any].f.{Box}.g.[any]` is clean, and deleting `{Box}` makes it `[any].f.g.[any]`, which is not.

`absorbCoveredByAnyPrefix` is safe by L2 and in fact stronger: its loop runs to a fixpoint over
`accessor == ANY_ACCESSOR_IDX || isCoveredByAny(accessor)` (AT:886), so the node it returns has **no
top-level `[any]` and no top-level covered accessor at all** — grafting it under an `[any]` cannot form
the infix at that junction. `addParentFieldAccess` is safe because its graft point is a *fresh*
single-accessor root (AT:943).

**Two operations genuinely produce it**, and both are live:

1. **The concat graft, through `limitFieldAccess`.** Conclusion `[any].f.*`, delta `g.f.([any].S)`. At
   the `f`-node's frame, AT:1676 hoists the delta's `f`-subtree — `[any].S` — into `nestedAccessors`,
   and AT:1700 installs it as `f → [any] → S` *under the conclusion's `[any]`*. `f` is covered, so the
   result is the bad shape. Neither limiter stops it: the absorbing arm is gated on `parentEdgeIsAny`,
   which is false one level under `f` (AT:1690), and the hoist at :1676 operates on the **unabsorbed**
   delta. Note the receiver shape here is exactly the one `AnyFieldMarkExclusionTest.kt:321` builds.
2. **`removeAllAccessorChains`** (AT:1883-1927, live at `MergingTreeSummaryStorage.kt:66`). It deletes
   `chainLengthToRemove` edges whose labels lie in an SCC of the accessor graph and merges the subtree
   into the chain's top node (AT:1900). **The SCC set may contain uncovered accessors**, so L2 is
   violated: a node `f → {Box} → ([any] → S)` sitting under an `[any]`, with component `{f, {Box}}` and
   length 2, collapses to `[any].[any]`.

One conditional case to record rather than rely on: `collapseElementAccess` / `limitElementAccess`
delete `ELEMENT_ACCESSOR_IDX` and hoist, which is safe **only because the production strategy declares
elements covered** (`TaintAnalyzer.kt:71-73`). A future `AnyAccessorUnrollStrategy` that does not would
turn it into a producer.

#### Is the uncovered case reachable at all?

The collapse must not cross an uncovered accessor (§8.2), so `[any].X.[any]` for uncovered `X` is a
shape the representation has to tolerate. Whether the **analyzer ever builds one** is a different
question, and the answer is no — for all seven uncovered accessors, though by three quite different
mechanisms and with one of them unguarded.

The reduction that makes this checkable rather than enumerable: **`[any]` only ever enters a tree at
the root of a node**, via `prependAnyAccessor` (AT:787, sole caller AT:572). It gets *deeper* only by
having accessors prepended above it. So `X.[any]` requires either a site that prepends `X` over a node
already headed by `[any]`, or a site that grafts a fresh `[any]`-headed subtree under an existing `X`
edge — and there is exactly one grafter, `concatToLeafAbstractNodes` (AT:1641-1705), which requires an
**abstract node directly under the `X` edge** to graft into.

| uncovered `X` | `[any]` below `X`? | `[any]` above `X`? | verdict |
|---|---|---|---|
| `[final]` | impossible — it is a flag, not an edge (AT:527, AT:2270 discards the accumulator) | n/a | **unreachable, structurally** |
| taint mark | **enforced** by `check(node.isStructurelessLeaf)` at AT:2204 | yes | **unreachable, enforced** |
| static | yes — `<static>(C).[any].![m].$` is an ordinary rule-position fact | **enforced** by the subtree-wide `containsStatic` guard at AT:547 | **unreachable, enforced** |
| `[value]` | — | — | **unreachable, vacuously**: `ValueAccessor` is never constructed anywhere in `src/main`; `TaintAnalyzer.kt:81` even `error`s on it |
| type-info / type-info-group | **nothing forbids it** — AT:2202 says outright that a type-info accessor may carry children | yes | **unreachable by construction-site accident, not by invariant** |

Three things follow.

**The union-without-collapse arm of `collapseNestedAny` is defensive, not load-bearing.** It costs
nothing when the population is empty, and §12.1 counts it so that stays a measurement rather than a
belief. §2.4's manager rule remains unconditional regardless — two `[any]`s on one branch multiply
whether or not the tree collapses them — but if the counter reads zero the arm can be promoted to an
assertion.

**Type-info is the fragile leg and it is worth closing.** The invariant holds only because both
front-end sites prepend onto a fresh `$` (`GoMethodCallResolver.kt:84,89` and
`JIRMethodCallResolver.kt:155`, consumed by `foldRight(createFinalAp(...)) { a, f -> f.prependAccessor(a) }`),
so structure is only ever added *above* a type-info accessor. One new flow function that prepends
`TypeInfoAccessor` onto an existing fact produces `{T}.[any]` silently, and `[any].{T}.[any]` follows
from a single `addParentIfPossible(ANY)`. A `check` that a type-info edge's child carries no `[any]`
would make that a loud failure instead of a quiet precision loss; it belongs with step 0.

**The load-bearing fact behind all of it is easy to lose:** TIFA never emits a chain terminating in an
always-unroll-next accessor (`createAbstractAp` is reached only at TIFA:325, :332, :338/:370, :364, and
`unprocessed` is pushed only with a non-always-unroll accessor or with `ANY`). Since both chain folds
seed with `abstractNode`, that is why `![m].*` and `{T}.*` do not exist — and therefore why the one
grafting site has nothing to graft into under a mark or a type-info edge. Change that and three of the
five rows above change with it.

For the record, `TreeInitialFactAbstraction.kt:353-356` reads as a counterexample and is not one. It
says *"The reachable shapes are `[any]` under `[value]` or under a type-info accessor"*, but it is
scoped to `forEachAccessor` — i.e. to `X.[any]`, not `[any].X.[any]` — it is an elimination argument
over the four always-unroll-next accessors describing what the loop must **tolerate** rather than what
the engine emits, and its `[value]` clause is stale.

#### Where to enforce it

Factor the body of `prependAnyAccessor` into the part that produces the normalised child:

```kotlin
// prependAnyAccessor() becomes  create(ANY_ACCESSOR_IDX, this.collapseNestedAny())
private fun collapseNestedAny(): AccessNode        // AT:789-806, unchanged, plus the id union of §4.1
```

and call it wherever an `[any]` edge is **installed** over a child. There are exactly three such places,
and the census confirms there is no fourth — *"no path in concat attaches an `[any]` edge to a node
without that node being built by AT:2221 or AT:2195"*:

| site | why it is needed |
|---|---|
| AT:2195 raw single-edge `create(accessor, node)` | `filterStartsWith`'s spine fold (:1750), `reconstructRemainder` (:721), and both chain folds (:2271, :2281) reach it with `[any]` |
| AT:2221 → AT:2243 the array factory | the only route for `bulkMergeAddAccessors` (:1119), `mergeAddStep` (:1170), `mergeAddDeltaStep` (:1220, :1228), `transformAccessors` (:1850) and `AnySuffixMatcher.kt:162` — i.e. **both producers above land here** |
| AT:2018 `Serializer.readAccessNode` | the one route that bypasses *both* factories, calling the private constructor directly |

The gate is two O(1) steps and needs no new state: `accessors` must contain `ANY_ACCESSOR_IDX`
(`containsAnyAccessor()`, a `binarySearch`, AT:499-500), and *that slot's child* must have
`containsAnyInThisOrDeepNodes`. The flag is a final field set in the child's own init block, so it is
readable **before the parent exists** — which is what makes enforcement at construction possible at all.
Every node with no `[any]` edge exits on the first test with no allocation. What reaches the worklist is
the population `prependAnyAccessor` already pays for today, plus the legitimate
`[any].<uncovered>.[any]` cases, which enter and leave it unchanged (`stripAnyBelowCoveredPath` hits
`else -> node`, `transformAccessors` reports no modification, AT:1849 returns `this`).

#### The one test this breaks

Exactly one assertion in the repo builds the shape on the fact side and depends on it surviving:
`AnyAccessorCollapseTest.kt:128`, `val uncollapsed = treeOf(node(AnyAccessor to fact.access))`, used as
an oracle at :129-140 to check that reads through the collapsed form match reads through the raw one.
Its `node(...)` helper (test :68-75) goes through the **array factory**, so normalising there makes the
oracle equal to the thing it is checking and that half of the test becomes vacuous. Rewrite :127-140 to
assert the reads against a hand-specified expectation; the first half (:115-126), which pins the
collapse itself, is unaffected.

Nothing else moves. The same helper's other uses (:175, :195) have no `[any]` beneath their `[any]`
child; `AnyAccessorPremiseTest`'s two-`[any]` assertions are premise-side and go through
`AccessPath.AccessNode` (AccessPath.kt:629-644), not either fact factory; and no other test in the repo
constructs `[any].<covered>*.[any]` as a fact.

**Depth-relative exclusions need no new bookkeeping, and this was checked rather than assumed** —
it is the obvious place for the change to be quietly unsound. `absorbCoveredByAnyPrefix` threads an
`absorbedAnyStep` flag into `filterDeepExclusion` (AT:735-745) precisely because absorption hoists
accessors under a *stationary* claim owner, so relative depths shrink and a depth-1 claim's start
exemption would silently free a mark. `stripAnyBelowCoveredPath` carries `deepAccessorExclusion`
verbatim on every hoisted node and has no analogue — and that is right for three reasons visible in
the code:

1. **The claim and its subtree move together.** A claim is depth-relative *to its own node*; hoisting
   relocates owner and content as one unit, so no relative depth inside the moved subtree changes.
   Absorption is the opposite situation, which is why C2 exists there and not here.
2. **Hoisting only moves content out from under a claiming ancestor**, so fewer claims apply, not
   more. That is the false-positive direction. `intersectDeepExclusion` (AT:1139-1143) is likewise a
   weakening join.
3. **Both claim-introduction sites already replicate the claim downward** as a depth-0 claim on every
   abstract descendant — `clearAccessorOccurrencesBelow` → `addAccessorFromDepth0` (AT:1014, :1030),
   and `filterDeepExclusion`'s `collapseToDepth0()` + `annotateAbstractNodes` (AT:760-764). So a
   descendant that is later hoisted already carries the claim in its strictest form.

One residual channel is worth naming rather than discovering: `splitOnMatching` refuses a match when a
claim is present (AT:677, AT:698), so any normalisation that moves a claim onto a node that previously
had none — reachable only through `intersectDeepExclusion`'s AT:1140 arm — can suppress a delta. That
is false-negative shaped, it is reachable from any ordinary `mergeAdd` today, and §12 counts it rather
than assuming it away.

**This is a behavioural change beyond the manager**, and it should be measured as one: it coarsens
facts the graft currently keeps precise, so it belongs behind its own gate in §12 and its own line in
the SARIF comparison, separable from `L`.

## 5. Where the charge happens

### 5.1 `getChild`'s covered arm is the unique synthesis point

Every concrete accessor that is materialised *out of* an `[any]` — as opposed to being read from an
edge the fact literally has — comes from one place:

```kotlin
// AT:526-544
fun getChild(accessor: AccessorIdx): AccessNode? {
    if (accessor == FINAL_ACCESSOR_IDX) return manager.finalNode.takeIf { this.isFinal }
    val node = getNodeByAccessor(accessor)
    val anyAccessorNode = getNodeByAccessor(ANY_ACCESSOR_IDX) ?: return node
    val anyChild = anyAccessorNode.getNodeByAccessor(accessor)
    var resultNode = mergeAddMaybeNull(anyChild, node)
    if (manager.isCoveredByAny(accessor)) {
        val anyAccessorNoRepeats = anyAccessorNode.clearChild(accessor)
        val originalAnyNoRepeats = anyAccessorNoRepeats.addParentIfPossible(ANY_ACCESSOR_IDX)
        resultNode = mergeAddMaybeNull(originalAnyNoRepeats, resultNode)
    }
    return resultNode
}
```

Two consequences, both load-bearing.

**(a) Putting the record here covers every caller at once.** This is the structural difference from
§1.3, which instrumented one caller (`filterStartsWith`) and was blind to the rest. `getChild` is the
funnel; `filterStartsWith`, `readAccessor`, `AccessTree.delta`, `Cleaner.cleanConcrete` and anything
added later all pass through it.

**(b) The arm destroys and rebuilds the `[any]` edge** — `clearChild(accessor)` then
`addParentIfPossible(ANY_ACCESSOR_IDX)` — so the returned node's `[any]` is a **fresh node**. That is
what makes R4 expressible at all: the fresh `[any]` can be given `M.child(a)` while the original keeps
`M`. Had the arm returned the original `[any]` node, the parent and child managers would be forced to
be the same state and the automaton could not be built.

### 5.2 Query reads must not charge

`getChild` has ten callers and they split cleanly into fact-producing and boolean:

| build — records | query — must not record |
|---|---|
| `filterStartsWith` AT:1734 | `equalTo` AT:593 |
| `AccessTree.readAccessor` AT:78 | `containsStrict` AT:613 |
| `NodeAccessTreeDelta.readAccessor` AT:171 | `containsThroughAny` AT:649 |
| `AccessTree.delta` AT:191 | `matchThroughAny` AP:246 |
| `splitOnMatching` AT:679 → `reconstructRemainder` AT:706 | `splitDeltaStrict` AP:334, AP:368 |

`TIFA:228` was listed as a recording site in an earlier draft and is not one: it calls
`getChild(ANY_ACCESSOR_IDX)`, and `isCoveredByAny(ANY_ACCESSOR_IDX)` is `false` by design (§5.3), so
the covered arm never runs. The `[any]`-zero-times descent materialises nothing and costs nothing.
`splitOnMatching` replaces it in the build column — it descends a premise and `reconstructRemainder`
re-creates the walked edges raw (AT:721), which is the same read-then-rebuild shape as
`filterStartsWith` and needs the same id carriage (§4.1).

So the design does require one enumeration — but a far more robust one than §1.3's. That predicate
asked *"does this shape indicate growth?"*, a guess about tree shapes that turned out to be wrong in
three independent ways. This one asks *"does this caller build a fact?"*, which is a property of the
call site, checkable by reading ten functions, and stable under future changes to tree shapes.

It also fails safely in the direction that matters: misclassifying a query as a build **over**-charges
(costs precision), while misclassifying a build as a query **under**-charges (a refill). The list
above is short enough to get right, and §12 pins it with a counter.

Mechanically this is a second entry point — `getChild(accessor)` unchanged for queries, and a
recording variant taking the manager for builds — not a flag on the hot path.

### 5.3 Refusal is absorption, not truncation

When `root.total >= L`, the accessor is not written above the `[any]`. Since `X.[any]` already denotes
`X.a.…` for covered `a`, declining to materialise `a` asserts more, not less.

The naive form of this is **unsound** and the trap is worth naming: the node `getChild` returns is
generally a *merge* of the `[any]` branch and any concrete branches (`mergeAddMaybeNull` at AT:535 and
AT:540). Dropping the prepend across the whole merged node would rewrite `a.f.S` as `f.S` on the
concrete branches — neither a superset nor a subset, so a genuine loss. The absorption has to
**split**: skip the step only on the `[any]`-rooted branch, keep it on everything else.

```kotlin
/**
 * Prepend [accessor] above this node, EXCEPT on the branch an `[any]` at this node's root already
 * denotes. `a.[any].R` is a subset of `[any].R` for covered `a`, so dropping the step there is a
 * monotone coarsening. Every other branch keeps the step: `a.f.S` and `f.S` are disjoint.
 */
private fun addParentAbsorbingAny(accessor: AccessorIdx): AccessNode {
    // Order matters: probe for the `[any]` edge FIRST, then ask about coverage. See below.
    val anyNode = getNodeByAccessor(ANY_ACCESSOR_IDX) ?: return create(accessor, this)
    if (!manager.isCoveredByAny(accessor)) return create(accessor, this)

    val absorbed = create(ANY_ACCESSOR_IDX, anyNode)                 // [any] branch, step skipped
    val rest = clearChild(ANY_ACCESSOR_IDX).takeIf { !it.isEmpty } ?: return absorbed
    return create(accessor, rest).mergeAdd(absorbed)                 // everything else keeps it
}
```

All four primitives exist: `getNodeByAccessor` (AT:496), `clearChild` (AT:952), `mergeAdd` (AT:1134),
`create` (AT:2194). No existing `[any]` primitive expresses this — `prependAnyAccessor` absorbs only
when the accessor *is* `[any]`; `absorbCoveredByAnyPrefix` requires an `[any]` edge *above* and would
consume the one being preserved; `trimAnyCoveredAndPushChildren` operates on merge operands.

The soundness boundary is pinned by an existing test:
`AnyFieldMarkExclusionTest.kt:318` — *an abstract node under a field under an any must not absorb* —
which is exactly the case the split respects.

Any coverage query added here **must** be guarded, and the guard is *structural*, not a safe wrapper.
`TreeApManager.isCoveredByAny` (`TreeApManager.kt:50-51`) delegates straight to the injected
`AnyAccessorUnrollStrategy`, and the one installed for the whole prescan phase
(`TaintAnalyzer.kt:133-135`) is `AnyAccessorDisabled`, whose `unrollAccessor` **throws** — it does not
return `false`. There is no `isCoveredByAnyOrFalse` in the repo and this design does not add one: a
swallowing wrapper would turn the prescan contract "no `[any]` reaches here" from a loud failure into
a silent mis-analysis. The idiom the codebase already uses is to reach the query only on a path that
has proved an `[any]` edge exists (`AccessTree.kt:886`, `AccessTreeAnySuffixMatcher.kt:133`) or to
short-circuit before it (`AccessBasedStorage.kt:151`, `AccessPath.kt:281`), which is why the sketch
above probes `getNodeByAccessor(ANY_ACCESSOR_IDX)` first. This bug has been hit once already, stalling
openmrs at `Progress: 1/7367` with zero findings.

Two related facts, both checked rather than assumed:

- **`isCoveredByAny(ANY_ACCESSOR_IDX)` is `false`** under the production strategy
  (`TaintAnalyzer.kt:70-83`: only `ElementAccessor` and `FieldAccessor` are covered), and the codebase
  depends on it — `AccessTree.kt:867-871` and `AccessBasedStorage.kt:148-151` both say so explicitly.
  So `getChild(ANY_ACCESSOR_IDX)` never takes the covered arm, never synthesises, and never charges.
  That is what makes TIFA:228's `[any]`-zero-times descent free (§5.2).
- **The accessor constants are `FINAL=3, ELEMENT=11, VALUE=19, ANY=27, TYPE_INFO_GROUP=35`**
  (`AccessorInterner.kt:94-112`) — the only indices stable across `TreeApManager` instances; everything
  else is assigned in first-encounter order per manager. §9 depends on this.

## 6. The premise side needs no manager

Checked rather than assumed, and the answer is clean: **a premise `[any]` is a key, and a key cannot
materialise anything.** Every site that interprets one only matches or navigates:

- **`AccessPath.splitDelta` / `matchThroughAny`** (AP:177-290) — its `[any]` arm fans out over the
  *fact's* existing children (`otherNode.forEachAccessor`), never over an accessor universe. It
  constructs only an `AccessPath` prefix chain, already has its own budget
  (`MATCH_THROUGH_ANY_STEP_LIMIT = 10_000`, AP:449), and runs **only** on the trace-resolution path.
- **`AccessTree.delta`** (AT:178-210) — a pure descent driven by the premise's literal chain. It does
  reach `getChild`'s synthesising arm, but with an accessor *supplied by the premise*: one lookup per
  link, not a fan-out.
- **`AccessBasedStorage.collectNodesContainsAnyAccessor`** (AccessBasedStorage.kt:137-156) — note the
  polarity: the `[any]` triggering this arm is the *fact's*; the trie keys are premises, and the
  expansion re-enters **existing** trie children only. The doc at `:130-135` proves termination on
  exactly that basis.

The structural clincher: a premise is a linear chain (`AccessPath.AccessNode.next`), so
`getStartAccessors` returns a set of at most one (AP:61-63). Even the generic
`readPositionWithAnyAccessorSplit` (`taint/FactReaderUtils.kt:85-125`), which fans out over start
accessors and works over both `FactAp` kinds, degenerates to a single step on a premise and only
fans out on a fact.

**The one enumerating loop in the codebase is `unrollAnyAccessors` (TIFA:125-172), and it prepends
onto a fact node.** So the manager stays entirely fact-side.

### 6.1 What the unroll actually charges

`AnyAccessorUnrollRequest` (TIFA:195-199) captures `state.added` — **the node that carries the `[any]`
edge, not the `[any]` subtree**. Two confirmations: the guard is `state.added.containsAnyAccessor()`,
which is the *shallow* predicate (AT:499-500), and `anyBranch` is computed separately afterwards at
TIFA:228 and is not what the request holds.

So the unroll charges the manager on `unrollRequest.node`'s `ANY_ACCESSOR_IDX` slot. And note what the
unroll does with it (TIFA:156-165 → :184-187): the **entire** node, `[any]` edge and all, is
re-parented under `currentAp . accessor`. Unrolling `R.[any].*` with `f` yields `R.f.[any].*` — the
`[any]` **edge survives the operation**; only the prefix above it grows.

It is tempting to read that as "duplicated, not consumed" and conclude that the copy simply keeps the
parent's id. **That is wrong, and it is a refill.** `R.[any]` denotes `R`, `R.x`, `R.x.y`, …;
`R.f.[any]` denotes `R.f`, `R.f.x`, … — a strict subset, with exactly one step spent. The unroll *is*
an R4 read, so the copy must take the **child** manager `M.child(f)`:

- keeping `M`: unroll `f` then `g`, then read `p` under each. Both `R.f.p` and `R.g.p` record
  `M.child(p)`, the second is free, and the automaton stays one level deep no matter how wide the fan-out.
  Two materialised paths cost one accessor.
- advancing: they record `M.child(f).child(p)` and `M.child(g).child(p)`. Two paths, two accessors.
  This is the "set of emitted paths" the manager exists to represent, and it is the only version that
  bounds a *population* rather than a *frontier*.

Mechanically this is a one-node rebuild of `filteredNode` with a new `anyId` before
`addReversedApParents` runs — the deeper and sibling `[any]`s in that subtree are untouched, because
only the top edge's language lost a step. R2/R3 still matter for the same reason as before: the copies
that *do* share an origin must not get two budgets.

### 6.2 A pre-existing memo that will disagree

`AccessPathTrieNode.unrollAccessors` (TIFA:462-469) is already a one-shot, commit-as-you-read memo —
but it is keyed on the **premise prefix**, while the manager is keyed on the **fact `[any]`**. The two
will disagree about which accessors are still available, and the memo has no un-take: an accessor it
grants is burned even if the manager then refuses it (TIFA:88-91 documents the same hazard for the
existing cap).

The design must decide the order deliberately: **consult the manager before the memo**, so a refusal
does not consume demand that a later, better-funded state could have served. §11 sequences this.

Ordering it that way opens a **check/record gap** that §8.3 originally denied existed. The budget is
consulted before `unrollAccessors`, but the fact is only materialised — and `accountUnrolledFact()`
only called (TIFA:164) — after four filters that can each skip: `unrollStrategy.unrollAccessor`, the
type-checker's `Reject`, a null `filterAccessNode`, and a null `addReversedApParents`. So a check does
not always produce a record. The direction is safe: the check is re-evaluated per accessor and records
are a subset of checks, so this can only *under*-spend, never overshoot. It is worth stating because
§8.3's "1:1, no batch gap" is true of `getChild`'s arm and not of this one.

### 6.3 The abstraction's own emissions must inherit, not mint

TIFA emits, per abstracted position, an **identity pair** `(P, P.*)` (TIFA:96-105): a linear premise
`AccessPath` and a linear-spine `AccessTree` built by `createAbstractNodeFromReversedAp`. When the
walk descends through Site B, `P` contains an `[any]` link — so the emitted *fact* carries an `[any]`,
and §4.1's table would have minted a fresh manager for it.

That is the §1.1b failure returning through a side door. The witness carries 64,467 premises; minting
per emission would restore a per-premise budget, differing from the rejected per-`(entry point, base)`
counter only in being finer.

It is also unnecessary, because a predecessor **does** exist and the walk is holding it. The `[any]`
in `anyAp = ReversedApNode(ANY_ACCESSOR_IDX, state.currentAp)` is not invented — it is the `[any]`
edge of `state.added`, whose `anyId` is right there. So:

- `AbstractionState` carries a `governingAnyId`, initialised to `null` and set to `state.added.anyId`
  wherever the walk crosses an `[any]` (TIFA:228 and the Site B descent at TIFA:262).
- the emit callback passes it to `createAbstractNodeFromReversedAp`, which uses it for **every**
  `[any]` link in the fold.

One id for the whole chain is not an approximation: the chain is linear, so all its `[any]`s are on
one branch, and §2.4 says they must be one manager anyway. This simultaneously discharges the
"two `[any]`s on one branch from a raw chain fold" case of §4.1.

Sharing here can only *reduce* the budget available to the emitted fact, so it is sound in the
direction §8.2 requires. And it is a tightening rather than a correctness fix: §4.4 shows that a
mint-in-isolation heals on first graft. What it buys is bounding §8.3's "late unions" overshoot — a
fact whose `[any]` is read through *before* any summary is applied to it spends from the transient
budget, and there are tens of thousands of such facts.

**None of this puts a manager on the premise side.** §6's claim survives intact: the id travels on
`state.added` (a fact) and lands on the emitted fact; the emitted `AccessPath` gets nothing. That
matters more than it looks — premise identity keys the entire demand system (`AccessPathInterner`, the
`AccessBasedStorage` tries, `object2IntMap<AccessPath>` at `MethodTreeAccessPathSubscription.kt:119`,
`Set<InitialFactAp>` map keys at `DefaultNDF2FSetStorage.kt:16`), and two premises that differ only by
an id annotation would be two demands.

## 7. The graft: the largest channel, and why it still takes no charge

§4.4 proves the structural claim — `concat` cannot manufacture an `[any]`; every one in a result
traces to an operand. So the graft places an existing `[any]` under a concrete prefix the callee
legitimately derived, and no accessor is invented. It needs propagation, not a charge.

That is worth dwelling on because the numbers make it counter-intuitive. At cap 0 on the conductor
witness, `concat` is the **single largest** deepening channel — 1,170,752 events against
`filterStartsWith`'s 657,633 — and 100% of them are `fromNothing`. A reader looking only at the
ranking would put the budget there.

Two things resolve the tension:

- **A large fraction of the ranked total is a measurement artifact.** `addParent/?` scores 1,062,285
  with `minDepth=0`, `step=0` and accessor `<root>`: those are `[any]` *mintings* at the root, counted
  as "deepening" only because the measure uses a `-1` sentinel for "input had no `[any]`". They are
  `getChild`'s own re-prepend (AT:539) — a fixed point, not a prepend. Any comparison against these
  numbers must exclude them.
- **`concat` is a seeder, not a loop.** Its output is a fact with a deep concrete prefix and an
  `[any]`, which is precisely the input the R4 loop then grows. Its modal step is 4–6 links in one
  call because it grafts at *every* abstract node of the receiver simultaneously; `filterStartsWith`'s
  is 2–3 because it lengthens one prefix per premise. Bounding the loop bounds what the seed can grow
  into; bounding the seeder would mean bounding ordinary summary application.

The manager still reaches this channel indirectly, which is the point: the delta's `[any]` is itself
produced by a covered read in `AccessTree.delta` (AT:191), and that read *is* charged (§5.2). A
refused read yields a coarser delta, and the graft then places the coarser `[any]`.

**This is the design's biggest open bet**, and §12.4 is written to settle it: if `concat`'s volume is
itself the problem rather than a consequence of what it is handed, the manager will not converge
conductor and the lever is elsewhere.

## 8. Correctness

### 8.1 Termination — and this time it is a population bound

Three quantities are monotone and none of them can be walked backwards. `total` only ever increases:
transitions are added, never removed, each addition charges `pathCount ≥ 1`, and a dag fusion sums two
pots. `pathCount` only ever increases, by the same argument. And the number of live representatives in
each DSU only ever decreases. So once `total ≥ L` no further accessor is materialised out of that
automaton, and nothing can un-say it.

Therefore **at most `L` distinct concrete prefixes are ever materialised out of any one `[any]`
origin** — with the caveat §2.6 makes explicit, that "distinct prefixes" is the path-weighted count and
not the transition count. That is a bound on the *population*, which is what §1.2 could not deliver:
the per-fact limit bounded each chain at `L` while allowing `breadth^L` chains.

The bound survives the automaton being **cyclic** (§2.5), and it is worth seeing why, because the
naive reading is that a cycle means an infinite language and therefore an unbounded population. It does
mean an infinite language. It does not mean an unbounded population, for two independent reasons: the
budget is charged per *transition created*, and a cycle creates no new transition on any lap after the
first; and `pathCount` is maintained incrementally rather than by traversal, so it stays finite on a
cyclic structure by construction. A cycle is the analysis reporting that a loop has folded — one fact,
not infinitely many.

The bound rests on two claims, and both are obligations rather than theorems:

1. **The branch invariant (§2.4) holds.** Without it, nested `[any]`s on one path hold separate pots
   and the population under one origin is `Lᵈ`, not `L` — the bound degrades to exactly the shape
   §1.2 was rejected for. §12.1 measures it.
2. **Origins are minted only where §4.1 says.** The census puts that at seven sites, of which one
   (`prependAnyAccessor`'s fast arm) is an unconditional mint and the rest inherit or carry. So the
   total is `L × (number of origins)`, and the origin count is bounded a priori only by how often that
   one arm fires on an `[any]`-free tree.

The two sites that genuinely have no in-process predecessor are **deserialisation** (§9) and
`SummariesIdStorageNode.finalAccess`, which rebuilds a fact from a storage trie key
(`MethodInitialToFinalApSummaries.kt:151-157` — the premise chain is the only thing in scope). Neither
is a standing refill: the first is bounded at one per cached summary, and the second heals on its
first graft (§4.4). The earlier draft also counted the two premise-chain folds here; §6.3 shows they
have a predecessor after all and must inherit it.

Note the origin count is bounded from above in one direction for free: unions only ever reduce the
number of live representatives (§3.1).

Note what is *not* bounded, deliberately: concrete chains built by ordinary field reads and writes.
Those consume — the accessor joins a monotonically growing exclusion set — and they converge. The
no-`[any]` control reached 13 links and finished `rc=0` in 43.8 s with byte-identical SARIF
(`2e6dd9bc2445a9a5`), against `rc=253` and 64,467 premises with `[any]`. The bound applies only to
accessors bought from an `[any]`.

### 8.2 Soundness

Refusal replaces a fact with a **superset**: `X.[any].*` ⊇ `X.a.[any].*` under the zero-or-more-covered
reading, because the `[any]` already ranges over `a`. Over-approximating taint can add false positives;
it cannot drop a true flow.

So **no value of `L`, including `0`, can lose a finding relative to `L = ∞`** — a property none of the
previous caps had (the per-context cap at 0 lost findings even when it completed). §12.3 states this
as a falsifiable prediction and tests it.

The one place this could go wrong is the split in `addParentAbsorbingAny` (§5.3): absorbing across a
merged node's concrete branches would rewrite `a.f.S` as `f.S`, which is neither a superset nor a
subset. That is why the primitive splits, and why `AnyFieldMarkExclusionTest.kt:317-334` is the test
that must stay green.

**A correction to the existing documentation, which §4.7 depends on.** `prependAnyAccessor`'s KDoc
(AT:776-779) calls the nested-`[any]` collapse "an identity, not an approximation", and
`2026-08-21-any-premise-design.md:422` repeats it as `[any].<covered sequence>.[any] ≡ [any]`.

Write `Σ` for the accessors `isCoveredByAny` accepts. `[any]` is `Σ*`, so the whole question is one
line of language theory:

```
Σ*  ⊇  Σ* · f · Σ*        for f ∈ Σ
```

The inclusion is **strict** — the left side also denotes every sequence with no `f` in it — so the
collapse is a **monotone coarsening**, exactly as the sibling KDoc for absorption honestly says at
AT:862-865, and not an identity. Nothing existing is unsound, because a superset of a taint fact can
only add false positives.

The same line settles the precondition, which is why it is worth writing this way: the containment
needs `f ∈ Σ`, and for `f ∉ Σ` it fails outright — `Σ* · {Box} · Σ* · g` contains paths through a
`{Box}` step that `Σ* · g` does not denote at all. Collapsing there would **lose** flows, not
over-approximate them. So "at most one `[any]` per path" is sound only as "at most one `[any]` per
*covered-only* stretch of a path"; §4.7's covered-only guard is that side condition, and
`AnyAccessorCollapseTest.kt:143-153` is the passing test that pins it.

The distinction that is easy to lose, because the two rules read alike:

| | scope | conditional? |
|---|---|---|
| the **tree** collapse (§4.7) | merges two `[any]` *edges* into one | **yes** — only across `Σ` |
| the **manager** invariant (§2.4) | one budget per root-to-leaf path | **no** — unconditional |

`[any].{Box}.[any]` keeps both of its edges and shares one pot. That is exactly what
`collapseNestedAny` does in its two arms: collapse where legal, union where not (§4.1).

The word "identity" matters for §4.7 beyond pedantry: a normalisation that is an identity may be
applied anywhere without thought, whereas a coarsening has a precision cost — hence its own
implementation step and its own SARIF gate.

### 8.3 Overshoot, and where it actually comes from

At `getChild`'s covered arm the check and the record are one accessor at a time — **1:1, no batch
gap** — so the classic "one check authorises many emissions" overshoot does not arise. TIFA's arm is
*not* 1:1 (§6.2: four filters sit between the check and `accountUnrolledFact`), but the gap only drops
records, never adds them, so it under-spends rather than overshooting.

The real source is **late or missing unions**. If two managers exist for what is semantically one
`[any]` origin, each can spend up to `L` before they meet, so the origin spends up to `2L`; with `k`
such managers, `kL`. Separate managers for one origin can only arise from:

1. **a propagation site that allocates instead of inheriting** — R1 firing where R2/R3/graft should
   have. This is the entire reason §4 enumerates the lifecycle exhaustively; a missed site is not a
   crash, it is a silent refill.
2. **deserialisation** — §9.
3. **interner fragmentation left un-unioned** — two ids that should be one representative, §3.4.

All three are design obligations rather than inherent slack, which is the useful property: overshoot
here is a bug with a name, not a tolerance to be budgeted for. §12 counts distinct managers per origin
so the obligation is measured rather than assumed.

**A branch-invariant violation is a different failure and must not be filed under this heading.**
Missing unions cost `kL` — linear in the number of stray managers, and self-healing as they meet.
Two managers on one branch cost `L²`, and `d` of them cost `Lᵈ`; nothing heals it, because the pots
are compounding rather than adding. That is why §2.4's four obligations get their own gate (§12.1)
and why implementation step 4 must not be passed with a failing count.

One over-count is deliberate and belongs here: a **cross-dag cascade** (§2.6) sets the fused `total`
to `total(dx) + total(dy)` rather than the size of the union. It over-states by the shared prefix set,
which refuses sooner — a precision loss in the sound direction, taken to avoid a full product
traversal on a rare path. §12 counts cascades; if they turn out not to be rare, the product is the fix.

### 8.4 Determinism, honestly

Which `L` prefixes get into the automaton before the cut fires depends on arrival order, so the result is
**order-sensitive in precision**. Three bounds on how much that matters:

1. **It cannot change soundness.** Every reachable automaton state yields a valid over-approximation
   (§8.2), so order can move the false-positive count, never the true-positive set.
2. **It is not new.** `unrolledFactCount` is already a sticky, order-dependent cut and the code says
   so (TIFA:395-401). This design moves order-sensitivity from a per-base counter to a per-`[any]`
   trie.
3. **Findings have been stable in practice.** `.github/workflows/ci-analyzer-owasp.yaml` asserts an
   exact trace total (`EXPECTED_TRACES: 2633`) on OWASP BenchmarkJava on every push to main.

But the schedule **does** vary, and this was checked rather than assumed: analysis runs on
`newFixedThreadPoolContext(availableProcessors() / 2)` with no knob; the per-unit
`PriorityQueue(EventComparator)` is not a stable order (its comparator returns 0 on ties and its
ordering keys mutate while elements sit in the heap); and accessor indices are assigned in
first-encounter order by a process-wide interner, then used to key open-addressed maps whose iteration
order drives premise generation. Across ten same-config runs the
`unvalidated-redirect-in-spring-app` codeFlow flipped between `MiscUtils.java:91` and `:94`, with
three distinct trace hashes in one arm. The schedule moves; it has simply not yet moved an endpoint.

§12.6 is the obligation this creates.

### 8.5 The id is in the fixpoint, so the fixpoint must still converge

§3.4 puts `anyId` in node identity, which puts it inside the analysis fixpoint, and the storage layer
acts on it: `mergeAdd`'s "unchanged" test is `===` on the result (`MethodEdgesFinalTreeApSet.kt:33`,
`MethodEdgesInitialToFinalTreeApSet.kt:100`, `MethodEdgesNDInitialToFinalTreeApSet.kt:34`), and
`enqueuedUnchangedEdges` is an `ObjectOpenHashSet<Edge>` (`EdgeCollection.kt:177`) whose `Edge` hashes
its `FinalFactAp`, hence the node, hence the id. A fact whose id changed is a **new** fact to the
worklist. Three things keep that bounded:

- **A union produces no delta** (§3.5). Receiver-preferred unions leave the accumulated fact's
  representative unchanged, so the guard passes and the fact stays out of the worklist. This is the
  main reason the fixpoint is not amplified at all, and it is the opposite of what an earlier draft of
  this document specified.
- **A mint cannot be loop-carried.** The only unconditional mint is `prependAnyAccessor`'s fast arm,
  guarded by `!containsAnyInThisOrDeepNodes`. Its *output* carries an `[any]`, so re-entering the same
  site with that output takes the slow arm and reuses (R2). A cycle mints once and reuses thereafter.
- **Ids per component only ever decrease.** A union reduces the number of live representatives and
  nothing increases it.

**The residual case is destroy-then-recreate**, where an `[any]` is consumed and a fresh one prepended
with no id carried across. §3.4's census finds one place this genuinely happens — `Cleaner.kt:181→185`
and `:209→214` — and puts the carried id on the `AccessTree` **wrapper**, which closes it without
touching node identity. `abstractOnly` (`JIRMethodSequentFlowFunction.kt:594`) erases the `[any]` and
never restores it, so it has nothing to carry and nothing to churn.

What is left un-argued is a re-creation at a *different* node from the destruction, which no carrier
can follow. That is measured rather than reasoned about: §12 counts mints per site, and mints whose
result is structurally equal to a node already seen. The residual risk is R17.

---

## 9. Persistence

Managers cannot be serialised — they are analysis state, not fact structure. The node wire format
(AT:1942-1974) writes a three-bit mask and nothing else, and there is **no version tag anywhere** on
the path: not on the node mask, not in `TreeSerializer.kt:21-48`, not in `ApSerializer`, not in
`EdgeSerializer`, not in `MethodSumariesSerializer.kt:23-34`, and not on the persisted entity in
`JIRSummariesFeature.kt:272-315` (whose `apModeId` discriminates the *backend*, not the format).
`loadSummaries` reads stale gzipped blobs from previous runs back with no validation at all.

The consequence for this design is small and should be stated rather than discovered: a deserialised
`[any]` arrives managerless and takes a fresh one under R1, i.e. a full budget. That is **sound**
(more budget only means less coarsening) and bounded at one refill per cached summary, but it is an
instance of §8.3's overshoot and it means a warm cache and a cold cache can produce different
precision.

**One id per deserialised tree, threaded down the read — not one per `[any]`.** `readAccessNode`
(AT:1976-2019) recurses into children and applies **no invariant re-normalisation whatsoever**: it
rebuilds whatever edges the wire carried, so a tree with nested `[any]`s on one branch comes back with
them intact. Minting per edge would violate §2.4 B4 on the first such tree. The read is a downward
recursion, so it carries the id the same way §4.4's graft does: mint at the root of the tree being
read, pass it down, reuse for every `[any]` encountered. That also matches what the mint *means* here
— one cached summary, one origin.

### 9.1 Ids do not cross a `TreeApManager`

`anyId` is only meaningful relative to the DSU that issued it, and the analysis installs **two**
`TreeApManager`s per run — `TaintAnalyzer.kt:135` swaps in `TreeApManager(AnyAccessorDisabled, …)` for
the prescan phase and `:154` swaps the real one back. A node carrying an id from the first manager,
read under the second, would resolve to an unrelated manager or to an id past `nextId`.

This was traced rather than assumed, and **no live path exists**: `resetApManager` replaces every
container that can hold an `AccessNode` — summary storage (`MethodSummariesUnitStorage.kt:16-19`),
both subscription managers and `loadedSummaries` (`TaintAnalysisUnitRunner.kt:96-107`), and per-method
`edges` / `unprocessedEdges` / `enqueuedUnchangedEdges` / `pendingSummaryEdges` / `initialFacts`
(`MethodAnalyzer.kt:1368-1387`) — while `selectPhase` clears the rule assumptions that hold
`InitialFactAp` (`TaintSinkTracker.kt:182-185`). Every interner is per-manager too
(`AccessTreeSoftInterner` takes the manager at construction; the shared `SoftReferenceManager` holds
only write-only soft refs and hands nothing back).

Two caveats worth carrying, because they are the reason this is a §13 risk and not a closed question:

- **Nothing enforces it.** The tree backend has no `check(manager === other.manager)`; the automata
  backend does (`AccessGraph.kt:444, 513, 543, 726`). `AccessTree(apManager, …)` will hold an `access`
  whose `access.manager` is a different instance without complaint.
- **A breach would corrupt silently, not crash.** Accessor indices past the five stable markers
  (§5.3) are assigned per manager in first-encounter order, so a stray node's `accessors` array would
  simply denote different fields. Adding `anyId` does not create this hazard, but it does add one more
  per-manager namespace to it — which is an argument for adding the `check` the automata backend
  already has, as a cheap side-benefit of this work.

No format change is proposed. If one is ever wanted, the free space is mask bits 3–7, and any
encoding that *adds bytes* would shift the stream under every subsequent `readInt()`/`readLong()` and
misparse every stale cache — so that would need a version tag first.

---

## 10. Configuration

| property | meaning | default |
|---|---|---|
| `opentaint.anyUnrollLimit` | `L`, the per-origin budget. `< 0` = unbounded, i.e. today's behaviour | chosen by §12.3 |
| `opentaint.anyManagerDiag` | counters: states minted by site, unions, cross-dag fusions, records, refusals, distinct managers per origin and per branch (§12.1), **live** dags and states against ever-minted (§3.8), and `pathCount` / `total` distributions at exit | `false` |

`opentaint.anyUnrollLimit` is already in `FORWARDED_TEST_PROPERTIES`
(`core/opentaint-common-build/src/main/kotlin/org/opentaint/common/DefaultConfiguration.kt:65`);
`anyManagerDiag` must be added.

Restore the property read at TIFA:517-518, which is currently hard-wired to `100` with the
`System.getProperty` commented out. Both the KDoc at TIFA:505-516 and the comment at
`DefaultConfiguration.kt:64` still claim the cap is off by default and read from a property; **both are
false today** and should be corrected as part of this work.

`L < 0` must reproduce today's behaviour exactly — no managers allocated, no records, no refusals — so
the feature is one flag away from off.

## 11. Implementation plan

Ordered so that steps 1–4 are **inert by construction** — the DSU, the manager, the id and the
propagation rules all land before anything reads them — and each step has a gate that can fail
independently.

0. **Force the nested-`[any]` collapse** (§4.7) — `collapseNestedAny` factored out of
   `prependAnyAccessor` and called at the three installation sites (AT:2195, AT:2221, AT:2018). **This
   step contains no manager at all**, which is the point: it is a behavioural change to the tree
   representation, it lands and is measured on its own, and if it costs precision that is knowable
   before any of the rest exists.
   Land the type-info `check` of §4.7 with it — same step, same reasoning, and it closes the one leg of
   the uncovered-accessor argument that nothing currently enforces.
   *Gate: `AnyAccessorCollapseTest.kt:143-153` and `AnyAccessorPremiseTest.kt:139-143` green (the
   covered-only precondition); `AnyFieldMarkExclusionTest.kt:317-334` green (`.*` is not a collapsible
   tail); `AnyAccessorCollapseTest.kt:127-140` rewritten off its now-vacuous raw oracle; the two
   producers of §4.7 covered by new tests — a concat graft through `limitFieldAccess`, and
   `removeAllAccessorChains` over an SCC containing an uncovered accessor; the new type-info `check`
   firing on a hand-built `{T}.[any]` and on nothing in the suite; and a full SARIF comparison on
   openmrs, tms and conductor, reported **separately from `L`**.*
1. **`AnyUnrollState` / `AnyUnrollDag`** (§2, §3.3) — the two objects, the pointer `find` with path
   halving, and `union` writing `parent`, `pathCount` and `total` inside one lock. There is no DSU
   class and no id space: this step is two small classes.
   *Gate: single-threaded correctness (find/union/receiver-preference); the `pathCount` update being
   atomic with the `parent` write; a **forest-acyclicity** test — N threads issuing `union(x, y)` and
   `union(y, x)` on the same pairs concurrently, asserting `find` always terminates, which is the one
   failure §3.3 shows is a hang rather than a wrong answer; a concurrency test asserting every `find`
   returns the current representative and never a superseded one and that no `pathCount` increment is
   lost; and a **reclamation** test — drop the last reference to a merged-away state and assert it is
   collected (`WeakReference` + `System.gc()`), which is the property §3.8 rests on.*
2. **The automaton on `TreeApManager`** (§2, §2.2, §2.6): the two DSUs, the `edges` transition map,
   `pathCount`, `total` at the dag, the two-layer `union` with its same-dag precondition, the
   memoised product merge (§2.2), and the dag fusion that precedes any cross-automaton state merge.
   Nothing reads it yet.
   *Gate, and this is the step where cycles have to be proved rather than hoped: one successor per
   accessor after merging two overlapping automata; `union(X, X)` idempotent; **`union(m, m.a)`
   terminates, produces the self-loop, and leaves `m.pathCount == 2`** (§2.5); a second read of `a` at
   `m` afterwards mints nothing and charges nothing; `mergeStates` on two mutually reachable states
   terminates; a cross-dag union fuses the dags, merges their start states and leaves exactly one
   `total`; `mergeStates` across dags without a prior fusion is rejected, not silently accepted. Full
   suite green.*
3. **The state reference on the node.** `anyId` in identity (§3.4), the
   `anyId != null ⟺ ANY_ACCESSOR_IDX ∈ accessors` check in the init block, `find()` canonicalised at
   construction with `===` / `anyId.id` at compare time, plumbed through the five private-constructor
   sites (AT:1494, 2018, 2180, 2210, 2254), the `create` overloads and every `manager.create(...)`
   caller per §3.7. Still inert.
   *Gate: §12.7 (layout + node counts); with `L < 0` every node's `anyId` is `null`, so `flags`, `hash`
   and every comparison are bit-identical to today — assert that rather than assuming it; a unit test
   that a union does not change any live node's `hashCode`; and the reclamation test of step 1 repeated
   end to end.*
4. **The lifecycle rules.** Allocate / union / propagate at every site in §4.1–§4.5. Specifically
   including, because a census found each of them missing from the first draft: the `filterStartsWith`
   spine rebuild (AT:1750) and `reconstructRemainder` (AT:721) carrying the consumed id; the
   forced normalisation at all three installation sites (§4.7), which subsumes the graft case (§4.4);
   the uncovered-accessor union inside `collapseNestedAny` (§4.1); the `bulkMergeAddAccessors` entry
   state (§3.7); the delta node's state (§3.7); and the N-way unions (§4.6.1) accounted on the
   **completed** union. Still no charge and no refusal.
   *Gate: §12.1, now two counts — distinct managers reachable from one origin must be 1, **and
   distinct managers on any single root-to-leaf path must be ≤ 1** (§2.4). This is the step that
   either works or does not; do not proceed past a failing count. The branch count is the more
   important of the two, because §8.3 shows its failure mode is `Lᵈ` rather than `kL`.*
5. **R4/R5: record and charge.** The covered-read record at `getChild`'s arm, charging `pathCount` and
   not 1 (§2.6), plus the build/query split (§5.2) as a second entry point rather than a flag on the
   hot path. Recording only — nothing is refused yet.
   *Gate: §12.5 (query callers record zero) and §12.4 (records track the `fromAny` population). This
   is where the design is compared against the 657,633 baseline and against the prototype's 1,448.*
6. **The refusal.** `addParentAbsorbingAny` (§5.3) and the budget test `anyId.find().dag.find().total < L`.
   *Gate: §12.2's superset check on openmrs and tms; a new shape-asserting `filterStartsWith` test;
   `AnyFieldMarkExclusionTest.kt:318` green.*
7. **TIFA integration.** Consult the manager **before** `AccessPathTrieNode.unrollAccessors` (§6.2),
   so a refusal does not burn premise demand that a better-funded state could have served.
   *Gate: the seven cap tests in `AnyPremiseAbstractionTest`, extended for the manager.*
8. **Retire `unrolledFactCount`** (TIFA:401-408) and restore the property read at TIFA:517-518, which
   is currently hard-wired to `100`.

Step 0 is the only one that changes behaviour before `L` is ever set, and it is deliberately first and
alone so that its cost is attributable. Steps 1–4 then land behind `L < 0` with no behavioural change
at all, which makes the risky part (5–7) a small, separately revertable surface.

## 12. Validation

### 12.1 The two lifecycle obligations — gate everything

**(a) One origin, one manager (§8.3).** Tag each manager with the site that allocated it and count
**distinct managers reachable from one origin**. Expected 1. Anything above 1 names a propagation
site that allocates where it should inherit, and every such site is a silent budget refill. Report the
count *by allocating site*, because the number alone does not say which of the seven §4.1 sites leaked.

**(b) One branch, one manager (§2.4).** Walk each stored fact tree and, per root-to-leaf path, count
distinct `find(anyId)` values among the `[any]`-owning nodes on it. Expected **≤ 1**; report the max
and the offending path when it exceeds. This is the stronger gate and the one to trust: §8.3 shows (a)
failing costs `kL` and self-heals as managers meet, while (b) failing costs `Lᵈ` and does not heal.

A cheap always-on version of (b) belongs in the assertion budget rather than the diag flag: at every
site that creates an `[any]` above a subtree, assert that the subtree's `[any]` ids all `find` to the
id being written. That catches B1 and B4 at the point of failure instead of at a whole-program count.

Also count, under the same flag: unions, **cross-dag fusions** (§8.3 — the design assumes these are
rare and over-counts when they happen), live dags and live states against states ever minted, records
refused, and — the one that settles a standing question — **how often `collapseNestedAny` takes its
union-without-collapse arm, broken down by the separating accessor**. §4.7 concludes that population is
empty in production, and predicts *which* accessor would show up first if it is not: type-info, the one
leg of the argument that no check enforces. Zero across the witnesses means the arm can be promoted to
an assertion; a non-zero type-info count means a front end started adding structure below a type-info
accessor and §4.7's third bullet has become live.

Run all of this before any tuning. A design whose bound leaks is not worth sweeping.

**Four unit tests the audit says are missing or newly load-bearing**, all in
`.../access/tree/` where the existing `[any]` tests live:

1. **The graft under a concrete parent edge — the gap.** A grep for `parentEdgeIsAny`, "C4",
   "concrete field" and "must NOT absorb" across the test tree finds nothing;
   `AnyFieldMarkExclusionTest.kt:267-281` pins only the absorbing path. Add the mirror: receiver
   `[any].f.*` concat delta `[any].g.$`, assert the result is `[any].f.[any].g.$` (it is — §2.4 traces
   why nothing normalises it) **and that both `[any]` edges resolve to one dag**. This is B2's only
   direct test.
2. **The uncovered-accessor branch.** `AnyAccessorCollapseTest.kt:143-153` already asserts
   `[any].{Box}.[any].$` survives a prepend; extend it to assert the two edges share a dag. That test
   is now doing double duty — it pins both the tree shape and the manager rule that the shape forces.
3. **The cycle.** §2.5's scenario as a unit test on the manager alone: `union(m, m.a)` terminates,
   leaves `m --a--> m`, sets `m.pathCount = 2`, and a subsequent read of `a` at `m` mints nothing and
   charges nothing.
4. **Interning under the token.** `AnyAccessorCollapseTest.kt:107, 120, 152, 188` and
   `AnyPremiseAbstractionTest.kt:210, 258, 275, 289` compare nodes structurally and will start
   depending on both sides carrying the same id. Worth a deliberate pass rather than a surprise. Note
   `AnyFieldMarkExclusionTest.kt:452-456` round-trips through the serializer, which carries **no**
   token (§9) — so that test pins the mint-on-read behaviour whether or not anyone intended it to.

### 12.2 The consumer contract — gates §5.3
Force the absorption on *every* covered read (i.e. `L = 0` on that path only) and assert the three
`filterStartsWith` consumers in `MethodTreeAccessPathSubscription` produce a **superset** of the
baseline SARIF on openmrs and tms. Any *lost* finding refutes the claim that the consumers tolerate a
coarser-but-still-matching result, and selects the fallback of allowing one more link before refusing.

The existing `filterStartsWith` test (`AnyAccessorCollapseTest.kt:194`) asserts non-null only, not
shape, so it will not catch an absorption regression — a shape-asserting test is needed.

### 12.3 Soundness and the choice of `L`
Sweep `L ∈ {0, 1, 4, 16, 64, 256, ∞}` on openmrs, tms, thingsboard, conductor. Record `rc`, wall,
peak RSS, premise count, SARIF set, and the final `factDepthLimit` the resume ladder reached (so an
arm that was merely early is not scored as converged).

**The prediction to state before the run:** every finite `L` must produce a **superset** of `L = ∞`'s
findings, and conductor must reach `rc = 0` at some finite `L`. If a finding present at `L = ∞` is
absent at a finite `L`, §8.2 is wrong and this needs rework, not tuning.

Then choose the smallest `L` that converges conductor and leaves openmrs/tms/thingsboard
SARIF-identical.

### 12.4 The `fromAny` / `fromNothing` split — the design's biggest bet
Re-run `AnyPrependDiag` (default-off, on the `saloed/16`–`saloed/30` diagnostic stack) alongside the
manager. The cap-0 baseline to beat, on the conductor witness, excluding the `addParent/?` artifact
(§7):

| site | deepened | provenance |
|---|---:|---|
| `concat` | 1,170,752 | `fromNothing` |
| `filterStartsWith` | 657,633 | `fromAny` |
| `addParent/alias` | 33,578 | `fromAny` |
| `addParent/source` | 6,058 | `fromAny` |
| `abstractionFact` | 3,603 | `fromNothing` |
| `addParent/fieldWrite` | 662 | `fromAny` |
| `identitySummary` | 404 | `fromNothing` |

**What success looks like:** the manager's record count tracks the `fromAny` population (697,929), and
`concat`'s count falls *as a consequence* of being handed coarser deltas — not because anything
charged it.

**What failure looks like:** `concat` stays near 1.17M while the manager's records are capped. That
would mean the graft's volume is independent of what it is handed, the seeder argument of §7 is wrong,
and the lever is elsewhere. Run this arm **before** the `L` sweep — it is cheaper than the sweep and
it can invalidate the approach outright.

Also compare against the narrow prototype's numbers so the improvement is attributable: `AnyDeepen` at
`limit=100` charged 103 and refused 1,345 — 1,448 events against a 657,633 population, i.e. **0.2%**
of its own channel and 0.05% of the broad measure.

### 12.5 The query/build split — gates §5.2
Count records attributed to each of the ten `getChild` callers. The five query callers
(`equalTo`, `containsStrict`, `containsThroughAny`, `matchThroughAny`, `splitDeltaStrict`) must record
**zero**. A non-zero count there is an over-charge that will trip the cut early and coarsen facts that
were never growing.

### 12.6 Run-to-run stability — gates §8.4
**This has never been run**: no CI job and no in-repo harness analyses the same project twice and
diffs. Three requirements, each of which the obvious version gets wrong:

- **Diff the whole SARIF including `codeFlows`.** The usual `findings.tsv` digest is blind to the
  variation already observed, because its fingerprint uses only `trace.firstOrNull()`
  (`SarifGenerator.kt:139-146`, `:159`).
- **Pick a project that converges**, and raise the timeout. Timeout-bound runs are not reproducible
  even in principle — phase budgets derive from *measured elapsed time* (`TaintAnalyzer.kt:137`,
  `:156`) and a memory-pressure detector can cancel the run. Same-jar conductor pairs already differ
  in progress (2,528,446 vs 2,491,067).
- **Land the interner race fix first** (R10).

### 12.7 Heap — gates §3.4 and §3.8
The layout was computed field by field rather than guessed (HotSpot 64-bit, compressed oops, 12-byte
header, 8-byte alignment; `interned`/`isAbstract`/`isFinal` are constructor parameters, not fields, and
`AccessNode` is nested rather than inner so there is no outer reference):

```
 0..11 header | 12 int maxDepth | 16 long hash | 24 long size
 32..48 five oops: manager, deepAccessorExclusion, accessors, accessorNodes, anySuffixMatcher
 52 byte flags | 53..55 tail padding
```

41 bytes of fields, 53 total, **56 aligned, with 3 spare tail bytes**. Adding a reference (a 4-byte
compressed oop) gives 57 → **64**; so would an `Int`, and so would a `Long` (61 → 64). All three cost
**+8 bytes**, which is why §3.1 can take the reference without paying for it. A `Byte` or `Short` would
have been free, landing in the tail padding, as are the three unused `flags` bits (AT:2031-2035) — but
nothing in the final design needs them, because dormancy moved to the wrapper (§3.4).

Report the **live automaton** separately from the node cost, because §3.8's whole claim is that it is
reclaimed: live dags, live states, live transitions, and — the property the design rests on — that a
merged-away state with no remaining `AccessNode` holder actually becomes unreachable. A heap dump at
exit that still contains states from origins whose facts are long gone refutes §3.1 directly.

**There is no JOL dependency in this repo** (no `jol`, `ClassLayout`, `objectSize` or `sizeOf` anywhere
in source or build files), so either add one for this measurement or accept the hand layout above. The
in-repo proxy is `AccessNode.size` (AT:287), which counts *subtree nodes* and is already used as a heap
proxy at `TreeInitialFactAbstraction.kt:426-429`.

+8 bytes lands on the most numerous object in the analysis — the class doc records facts averaging 43
nodes across 2.6 M abstraction calls, 22,867 facts over 1000 nodes, and the target workload OOMing at
8 GB (AT:266-270). So measure the node **count** too, not just per-node size: putting `anyId` in
identity fragments the interner by ×(distinct origins touching a shape), and §3.4's dormancy adds a
second fragmentation axis on childless abstract leaves.

Report alongside it the §3.8 arithmetic as measured rather than projected: **mints** against **live
states**, since the gap between those two numbers is the entire case for references over arrays.

The fallback if it does not fit is to drop the id out of identity, which costs the per-origin scoping
(interning fuses toward one global manager) and is what §12.3 would then have to price.

### 12.8 The gate
`core/`'s bare `gradlew test` does **not** reach `opentaint-dataflow-core` — it is an included build,
and a bare `compileTestKotlin` does not reach its test source set either. Name tasks explicitly.
Baselines: 212 (opentaint-dataflow), 735 (core root), 3405 (full gate).

Tests that constrain this change and must stay green:

| test | pins |
|---|---|
| `AnyFieldMarkExclusionTest.kt:318` | the absorption soundness boundary — only the immediate parent edge licenses absorption |
| `AnyAccessorCollapseTest.kt:116` / `AnyAccessorPremiseTest.kt:102` | `X.[any].f.[any] → X.[any]`, fact and premise sides |
| `AnyAccessorCollapseTest.kt:194` | `filterStartsWith` still matches a premise longer than the `[any]` depth charge |
| `AnyAccessorPremiseTest.kt:211` | `size` is the literal link count; `depth` charges `[any]` at 10 — the prefilters compare `maxDepth` against `AccessPath.size` |
| `AnyPremiseAbstractionTest.kt` (7 cap tests) | the coarse `[any]` premise/final pair TIFA emits on exhaustion |
| `AccessBasedStorageAnyLookupTest.kt:112-347` | the **pull** path's `[any]` lookup; `AccessBasedStorage.kt:67-70` states pull and push must agree |
| `FactCleanerContractTest.kt` | cross-backend cleaner behaviour (its strategy covers nothing, so absorption never fires — keep green, constrains little) |

### 12.9 Other backends
**The cactus backend does not have this bug.** Its `getChild` (`AccessCactus.kt:554`) is a plain edge
lookup with no `isCoveredByAny` arm — `anyAccessorUnrollStrategy` is stored by `CactusApManager` and
never consulted anywhere in the package — and its `filterStartsWith` (`AccessCactus.kt:1010`) rebuilds
from the *query* rather than folding the walk history back on. So it needs no manager, but it also
cannot serve as a control: the two backends differ in the mechanism under test.

---

## 13. Risks

| # | risk | severity | mitigation |
|---|---|---|---|
| R1 | **`concat`'s volume is independent of what it is handed**, so bounding the loop does not bound the seeder and conductor still does not converge | **highest** — invalidates the approach, not a tuning failure | §12.4 runs before the sweep because it is cheaper and decisive. `concat` is 1,170,752 events at cap 0 against `filterStartsWith`'s 657,633 |
| R1b | **A branch-invariant violation (§2.4)**: two managers on one root-to-leaf path make the population `Lᵈ` instead of `L`. Unlike R2 this does not self-heal, and the four ways it can happen are all in code the first draft did not cover | **highest after R1** | §2.4's four obligations; §12.1(b) counts distinct managers per path and gates step 4; the always-on assertion catches it at the creating site |
| R2 | A propagation site allocates instead of inheriting — a silent budget refill. The `parentEdgeIsAny == false` graft (§4.4) is the most-executed one in the engine | **high** | §4 enumerates every site; §12.1(a) measures distinct managers per origin *by allocating site*, expected 1, and gates step 4 |
| R2b | The two **raw spine rebuilds** — `filterStartsWith` AT:1750 (657,633 events at cap 0, the largest read channel) and `reconstructRemainder` AT:721 — re-create `[any]` edges without going through `prependAnyAccessor`. Minting there refills per subscription match; dropping the id strands every manager at the first storage hop | **high** | §4.1 lists both; the linear walk makes carrying the consumed id mechanical |
| R3 | `anyId` in identity costs +8 bytes/node and fragments the interner by origin count | **high** — heap is the binding constraint | §12.7 measures size and node count; the fallback is dropping it out of identity, which trades precision for heap and re-opens global fusion |
| R4 | §5.3's consumers require structural prefix-equality, so absorption loses a finding | high — redesign, not a tweak | §12.2 checks it before the refusal lands |
| R5 | `markInterned` (AT:1494) drops `anyId`, exactly as it deliberately drops `anySuffixMatcher` | high but mechanical | in identity means a constructor parameter with no default, so it is a compile error rather than a silent refill (§3.4) |
| R6 | **Two concurrent unions on the same pair create a cycle in the DSU forest and `find` spins forever.** A racing stale read or a lost halving write are the benign cousins of this and are not the problem | **high** — the failure is a hang, not a wrong answer, and nothing detects it | §3.3: `find` and the parent write are inside one critical section for a union, which is what keeps the forest acyclic; halving stays lock-free only because its write set is disjoint from `union`'s. Step 1's gate is a concurrent `union(x,y)` / `union(y,x)` test asserting `find` terminates |
| R7 | N-way unions accounted incrementally instead of on the completed union, double-counting shared prefixes | medium | §4.6.1 — the trimming of §4.2 fires *inside* `stripAnyBelowCoveredPath`'s own merge loop |
| R8 | A deserialised `[any]` reaches a prescan-phase tree, where `AnyAccessorDisabled.unrollAccessor` **throws** | low but total (analysis stalls) | AT:2018 is the one `[any]` creation site that never consults the strategy; guard the coverage query. This class of bug has been hit once, stalling openmrs at `Progress: 1/7367` |
| R9 | The manager and `AccessPathTrieNode.unrollAccessors` disagree about which accessors remain, and the memo has no un-take | medium | §6.2 — consult the manager first; step 6 sequences it |
| R10 | The query/build split (§5.2) is misclassified — a build treated as a query under-charges | medium | §12.5 counts records per caller; the list is ten functions |
| R11 | Manager-state allocation churn adds GC pressure on a heap-bound workload | medium | one ~32-byte object per live state, bounded by `origins × (L+1)` (§3.8), and reclaimed when nothing holds it — which is the trade §3.1 makes deliberately against never reclaiming |
| R12 | An `L` small enough to converge conductor is coarse enough to add FPs elsewhere | medium | §12.3 requires openmrs/tms/thingsboard SARIF-identical at the chosen `L` |
| R13 | Order-sensitivity moves findings between runs | medium | §8.4 states the cost; §12.6 measures it — and it has never been run |
| R14 | The interner data race returns a wrong accessor index, diverging findings independently of this design | **high for measurement** | the fix `e082a4b72` is **not** on this branch — land it first, or every measurement is uninterpretable |
| R15 | Records lost at the two no-refund destruction sites (§4.6.2) make the automaton under-count | low | sound (the budget goes further, never shorter); §12's counters must treat `total` as a lower bound |
| R16 | `find` leaks into `hashCode`/`equals`, so a union changes a live node's hash and every hash structure holding it loses the entry | high but preventable by rule | §3.4: the stored reference at compare time, `find` at build time and in the merge guard only; step 3's gate asserts a union changes no live `hashCode` |
| R17 | The id is inside the fixpoint (§8.5) and a destroy-then-recreate cycle mints on every lap | medium | §3.5's no-delta rule removes the amplification; §3.4's wrapper-carried id closes `Cleaner`, the one genuine round trip. What is left — a re-creation at a different node — is counted, not argued |
| R18 | `InternStrategy.equals` (`AccessTreeInterner.kt:15-29`) is a *second*, different comparison from `AccessNode.equals` and already omits `deepAccessorExclusion`; forgetting `anyId` there fuses two budgets on a hash collision | medium, silent | §3.4 names all three places that must learn about the id |
| R19 | Cross-dag cascades are not rare, so the `total(dx) + total(dy)` over-count coarsens broadly | medium | §12.1 counts cascades; the fallback is the full product traversal |
| R21 | **The whole loop fixpoint rests on one reference comparison.** `mergedAccess === currentAccess` fires only because `mergeAddStep` returns the receiver, which holds only because the `[any]` child is the shared `abstractNode` singleton. Any field that makes structurally-equal nodes distinct objects costs every loop in the program extra laps | **high** | the id is non-zero only on `[any]`-owning nodes; dormancy is kept off the node entirely (§3.4); §12.1's cycle test pins it |
| R22 | The union is a **side effect** of computing the merged id, and an implementation that short-circuits the shape check before unioning skips it — then §2.5's self-loop never forms and **the analysis does not terminate** | **high**, and it looks like an optimisation | §3.5 states the ordering explicitly; §12.1's cycle test fails loudly if it is skipped |
| R23 | Mints do not collapse: 40k on the conductor witness would be a 4M population bound — worse than the 735k §1.1b rejected — and a correspondingly large live automaton | **highest, jointly with R1** | §3.8 shows memory and budget are the same measurement, so §12.1 answers both; §4.7, §6.3 and §3.4 all attack the mint count. There is deliberately **no valve**: if this fails it must fail visibly (§3.1) |
| R25 | §4.7's forced collapse costs precision — it is a coarsening, not the identity the existing KDoc claims (§8.2) — and it changes behaviour before any budget exists | **high**, but knowable early | it is implementation **step 0**, alone and first, gated on a full SARIF comparison reported separately from `L`. `TreeCleanerFieldSensitivityAnalysisTest`'s depth-3 pair is the end-to-end detector: a sanitizer must still bite after a graft |
| R26 | The collapse is enforced at construction, so an over-reach is total rather than local: dropping *covered-only*, or treating `.*` as a collapsible tail, silently rewrites facts everywhere | **high** | three existing tests fence it, one per over-reach (§4.7); each fails loudly and for a distinct reason |
| R28 | `[any]` under a **type-info** accessor is forbidden by nothing — AT:2202 permits children explicitly — and is kept out only by the two front ends prepending onto a fresh `$` and by TIFA never terminating a chain there. A new flow function prepending `TypeInfoAccessor` onto an existing fact reopens `[any].{T}.[any]` silently | medium, and silent | §4.7: add the `check` with step 0, and count the union arm by separating accessor (§12.1). Marks and statics are genuinely enforced; this one is not |
| R27 | Reclamation recovers less than it appears to — storages never delete, so states reaching a stored fact live for the phase | medium, and stated rather than hidden | §3.8; the argument for references does not rest on the constant factor but on the array version being unbounded on a long phase |
| R24 | `pathCount` approximates in both directions — over-stating live facts after a fact-merge, under-stating the language after a union whose increase is not pushed down | medium, deliberate | §2.6 states both, and both are `O(1)` choices; over-statement is the sound direction (§8.2) |
| R20 | `anyId` adds one more per-`TreeApManager` namespace to a codebase with no `check(manager === …)` in the tree backend | low — no live path found (§9.1) | traced through `resetApManager` and `selectPhase`; add the guard the automata backend already has |

---

## 14. What this design does not do

It bounds how far an `[any]` can be *unrolled*; it does not reduce the number of `[any]`s. The ten
`$*` whole-object source markers that seed the conductor blow-up — worth 16–37× on their own — are
untouched. If `L` has to go very low to converge conductor, that is evidence the source rules are the
better lever and this bound is treating a symptom. §12.3's sweep is what tells them apart.
