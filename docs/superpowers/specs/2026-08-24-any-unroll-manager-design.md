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
| the branch invariant was never stated, so the bound was `Lᵈ`, not `L` | §2.4, with its four maintenance obligations |
| `parentEdgeIsAny == false` was read as "no `[any]` above" — it is a one-level memory | §4.4: `governingAnyId` threaded down the receiver spine |
| `filterStartsWith` AT:1750 and `reconstructRemainder` AT:721 re-create `[any]` edges raw; both were absent from the site table. AT:1750 is 657,633 events at cap 0 | §4.1 |
| the manager had no `originId`, so `total` was per-trie-position and §1.2's branching returned | §2, and the origin/representative distinction spelled out |
| the TIFA unroll was to "share" the parent id; it consumes a step, so it must advance to the child | §6.1 |
| TIFA's own emissions were to mint per premise — the §1.1b failure through a side door | §6.3: inherit the walk's governing id |
| `find` was to be stored *and* compared, which makes `hashCode` change under a union | §3.4: raw at compare time, `find` at build time and in the guard |
| §5.3's sketch called `isCoveredByAnyOrFalse`, which does not exist and must not | §5.3: probe for the edge first |

Two claims the audit **confirmed** rather than corrected: no `AccessNode` crosses a `TreeApManager`
boundary (§9.1), and `isCoveredByAny(ANY_ACCESSOR_IDX)` is `false`, so the `[any]`-zero-times descent
is free (§5.3). One new termination question was opened and answered: §8.5.

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
It holds a trie of the concrete accessor prefixes that have been materialised out of that `[any]`, and
its total node count is the budget measure.

The node does not point at it. The node carries an **int id**; `TreeApManager` owns a DSU over those
ids and a map from **representative** to manager object (§3):

```
AccessNode.anyId : Int                          // 0 = none; non-zero IFF this node owns an [any] edge

manager = {
    originId: Int,                              // the id of the trie ORIGIN this node belongs to
    children: Int2ObjectMap<manager>,           // accessor -> child manager (the trie)
    total:    int                               // emitted accessors -- MEANINGFUL ONLY AT THE ORIGIN
}
```

`originId` is a distinct thing from the DSU representative, and conflating the two is the easiest
mistake in this design. The **representative** is what `find` returns — it names the equivalence class
of ids after unions. The **origin** is the trie root: the `[any]` occurrence this manager descends
from by R4. A node deep in the trie has its own id *and* representative, but it spends from its
origin's pot:

```
budget(node) = managers[dsu.find(managers[dsu.find(node.anyId)].originId)].total
```

Without the origin, `total` would be per-trie-position, and the branching of §1.2 walks straight back
in: reading `a` then `b` from one `[any]` would give two positions each with its own `L`. With it,
every position under one origin reads and writes one number. This is the user-stated rule "each
any-manager knows its root".

Four rules govern its lifecycle:

| # | event | rule |
|---|---|---|
| R1 | an `[any]` edge is **created** where none existed | mint a fresh id (§4.1 lists the sites); the manager object itself is allocated lazily on first record |
| R2 | an `[any]` is prepended onto a tree that **already has** one or more `[any]`s | union **all** of them and reuse the result — never mint (§2.4 B1) |
| R3 | two trees **merge** | `union(this.anyId, other.anyId)`, receiver preferred as the new root (§3.2); the merged node carries the representative |
| R4 | an accessor `a` is **read through** an `[any]` | record `a` in the manager and charge the origin; the resulting deeper `[any]` carries the id of the **child** manager for `a`, which inherits the same `originId` |

R4 is where the budget is both charged and consulted: `total` is read and written at the **origin**, so
every branch under one `[any]` origin spends from one pot. That is §1.2's requirement. R3 is what makes
convergent derivations share rather than double-count — and because it is a **union of tries**, not a
sum of counters, re-deriving a path is free with no novelty signal needed anywhere.

Two consequences of R4 that are worth stating because they are not obvious:

- **The trie records derivation order, not tree depth.** R2 can put a manager that sits at trie depth
  3 onto an `[any]` edge at tree depth 0. That is correct and in fact desirable: the trie is a
  canonical name for *the sequence of reads that produced this `[any]`*, which is exactly the thing
  that must not be paid for twice.
- **Most ids never get a manager object.** An `[any]` that is never read through records nothing, so
  `managers` is a sparse map: absent entry means empty trie, `total = 0`. Given the mint sites are hot
  (§4.1), lazy allocation is the difference between one object per `[any]` occurrence and one per
  `[any]` that is actually enumerated. §12.7 counts both.

**Cross-origin unions cascade.** `union(x, y)` where `x` and `y` have different origins means two
tries have fused at a non-root position, so the two pots have to become one: union the origins as well,
and set the surviving `total` to `total(Ox) + total(Oy)`. The sum over-counts the prefixes the two
tries shared, which errs toward refusing sooner — a precision loss, never a soundness one (§8.2) — and
it avoids a full trie product on a path that is rare. §12 counts cascades so the "rare" is measured
rather than assumed.

### 2.1 Ownership: `TreeApManager` allocates and unions

Allocation (R1) and union (R3) are `TreeApManager`'s responsibility, not the nodes'. It is the single
object every tree-backend site already holds — `TreeInitialFactAbstraction(this)` at
`TreeApManager.kt:54` and `MethodTreeAccessPathSubscription(this)` at `:77` — and it is the only
common ancestor of the two spend sites, which live under different owners (TIFA under the callee's
`NormalMethodAnalyzer`, the subscription under the caller's `SummaryEdgeSubscriptionManager`).

A manager is reached as `managers[dsu.find(node.anyId)]`, so `total` is a `find` plus one lookup rather
than a walk, and every node carrying any id in the set reaches the same object (§3.1).

### 2.2 The union is a DFA product, not a root repoint

This is the part that is easy to get wrong. The manager structure is a **DAG** — sub-tries are shared
after unions — and it must behave as a **DFA**: from any node, one accessor leads to exactly one
successor. Two DAGs in, one DAG out.

A naive DSU union that just repoints one root at the other leaves two successors for the same
accessor, i.e. an **NFA**. Every subsequent lookup would have to explore a set of states, the trie
would stop being a trie, and `total` would double-count the prefixes the two sides shared — which is
exactly the property (§2) that makes re-derivation free.

The int-level `union` is what names the result; the trie-level merge is what makes it a DFA. Both are
`TreeApManager`'s job, and they happen together. The trie merge recurses:

```
union(X, Y):
    if X === Y: return X
    if memo[(X, Y)] exists: return it            // identity-keyed, breaks cycles in the DAG
    Z = new node; memo[(X, Y)] = Z
    for each accessor a in X.children ∪ Y.children:
        Z.children[a] = union(X.children[a], Y.children[a])   // one successor per accessor
    return Z
```

Structurally this is the operation `AccessTree` already implements for trees: `mergeNodeLoop`
(AT:1231-1282) is an explicit-stack merge with an identity-keyed memo (`AccessNodeMergePair`,
AT:1122-1132, hashed by `System.identityHashCode`). The same shape applies here, and the same reason
for the explicit stack applies — these structures are deep enough that recursion is a liability.

`total` after the union is `|X ∪ Y|`, computed as the merge proceeds, not `|X| + |Y|`. The merged trie
is stored under the surviving representative and the other entry is dropped, so a union frees a manager
object as well as merging one (§3.1).

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
  through `abstractAccessPath` (§6.3) and why `concatToLeafAbstractNodes` can carry a single one down
  the receiver spine (§4.4) — no sets, no joins, one int per stack frame.
- **A linear chain fold needs exactly one id.** `createAbstractNodeFromReversedAp` (AT:2266) folds a
  premise chain that may contain several `[any]` links; they are all on one branch by construction, so
  one id covers the fold (§6.3).

Maintaining it costs four obligations, each of which corresponds to a way a second `[any]` can come to
sit above or below an existing one on one path:

| # | how a second `[any]` lands on an occupied branch | obligation | where |
|---|---|---|---|
| B1 | prepend: a new `[any]` is placed **above** everything | union **every** manager in the subtree, not just "the inner one" | §4.1 |
| B2 | graft: a delta rooted at `[any]` is spliced **below** a receiver whose path already crosses an `[any]` | thread the governing id down the receiver spine; union at the leaf | §4.4 |
| B3 | merge: two trees are combined | per-position union, plus the fold-to-`[any]` trimming | §4.2 |
| B4 | raw reconstruction: an `[any]` edge is re-created by a spine rebuild or read off the wire | carry the consumed edge's id; one id per chain | §4.1, §9 |

B3 is the one that needs no extra machinery and it is worth saying why, because it looks like it
should. When receiver and arrival meet at position `p`, an `[any]` the receiver owns *at* `p` and an
`[any]` the arrival owns *below* `p.f` are **not on the same branch** — `p → [any] → …` and
`p → f → …` diverge at `p`. So the ordinary per-position union (R3) plus recursion is complete, and
the only extra source is `trimAnyCoveredAndPushChildren` folding one side's covered `f.[any]` **into**
the other's `[any]`, which §4.2 already lists as a union site. Hoists (`limitFieldAccessCached`,
`collapseElementAccess`) move `[any]`s *up*, which can only remove same-branch pairs, never create
them.

---

## 3. Representation: an int id in the node, a DSU in the manager

The node does not hold a manager reference. It holds a **small int id**, `TreeApManager` owns a
disjoint-set union over those ids, and the actual manager objects are bound to DSU **representatives**.

```
AccessNode.anyId : Int                     // 0 = none; only nodes carrying an `[any]` edge differ
TreeApManager:
    dsu      : concurrent DSU over ids           // find(id) -> representative
    managers : Int2ObjectMap<AnyUnrollManager>   // keyed by REPRESENTATIVE only
    nextId   : AtomicInteger
```

This is what makes the whole thing affordable. The two alternatives considered earlier both failed:
`anySuffixMatcher` hangs on the node *below* the `[any]` edge — overwhelmingly the `abstractNode`
singleton — so widening it would fuse every terminal `[any]` in the program into one manager before
any interning; and a plain manager reference is dropped by `markInterned` (AT:1494) exactly as the
matcher deliberately is, with none of the matcher's "pure function, safe to rebuild" justification.

### 3.1 Why an id rather than a reference

- **A union is an int operation.** Merging two managers rewrites no node: `union(a, b)`, and every node
  carrying either id resolves to the merged manager through `find`.
- **Stale ids are harmless.** A node built before a union keeps its old id and still `find`s to the
  right representative. Nothing has to be chased through the tree.
- **Unions free manager objects.** Because `managers` is keyed by representative, a union merges two
  tries into one entry and drops the other, so the live manager count **monotonically decreases**.
  That bounds the allocation churn of §13 R11.
- **It is four bytes**, not a reference plus an object per edge.

### 3.2 The union, and the preferred root

`union(this.anyId, other.anyId)` with **`this.id` as the preferred new root** — the receiver's
representative wins. In `mergeAdd(other)` the receiver is the accumulated, long-lived tree and `other`
is the arrival, so preferring the receiver keeps ids stable on the structure that persists and lets the
transient side's id die out.

Representative choice is **semantically neutral**: the union merges the tries by DFA product (§2.2),
so the merged content is identical whichever int survives — only the name differs. That matters for
determinism. The representative depends on merge order and therefore on schedule, but nothing
observable depends on it.

### 3.3 A dedicated DSU, not the existing one

`analysis/alias/IntDisjointSets.kt` is the in-repo DSU and its `union` picks the parent through a
strategy, which is the right shape:

```kotlin
// IntDisjointSets.kt:34-52
fun union(x: Int, y: Int): Boolean {
    val u = find(x); val v = find(y)
    if (u == v) return false
    val cmp = strategy.compare(u, v)
    check(cmp != 0) { "Strategy cmp is 0 for non-equal elements" }
    if (cmp < 0) merge(p = u, c = v) else merge(p = v, c = u)
    return true
}
```

**It is the wrong class to reuse.** Write a dedicated one.

What is wrong with it here:

1. **Not thread-safe.** It is written for the alias analysis, which is confined to one method's state.
   This DSU lives on the shared `TreeApManager` (§3.6).
2. **`find` is recursive** (`:25-32`) with unconditional path compression. These chains are as deep as
   the merge history, and the write on every read is exactly what a lock-free reader cannot do.
3. **`RankStrategy` is a stateless `IntComparator` over values**, so it cannot express "prefer the
   receiver's id" — that is a property of the call, not of the two ints. Its `check(cmp != 0)` also
   demands a total order over ids, which "prefer the receiver" is not.
4. **Map-backed** (`Int2IntOpenHashMap`), where our ids are dense and minted from a counter.

What it carries that we do not need, and would have to keep working: removal
(`removeAll`, `prepareRemoveAll`, `RemoveResult`, and the `NewSetRepr` re-rooting logic), set
enumeration (`forEachElementInSet`, `collectElementParentPairs`), and the immutable/copy protocol
(`ImmutableIntDSU`, `mutableCopy`, `equals`). Ids here are never removed and sets are never
enumerated — a manager is reached by `find`, never by walking its members.

The dedicated version, in full:

```kotlin
/**
 * DSU over `[any]`-manager ids. Ids are dense, minted from a counter, and never removed.
 *
 * `find` is on the hot path -- every covered read -- and is lock-free. `union` is rare and
 * synchronized. What makes the lock-free read safe: a parent link only ever moves TOWARDS a root,
 * never away, so following parents from a stale read still converges on the current representative.
 */
class AnyIdDsu {
    // Segmented, never copied: growth appends a segment, so a concurrent reader can never observe
    // a moved entry. An AtomicIntegerArray cannot grow, and copy-on-grow would let a racing `find`
    // return a representative that a union has already superseded.
    @Volatile private var segments: Array<AtomicIntegerArray> = ...

    fun find(x: Int): Int {
        var cur = x
        while (true) {
            val up = parentOf(cur)
            if (up == cur) return cur
            val grand = parentOf(up)
            if (grand != up) casParent(cur, up, grand)   // path halving, best-effort
            cur = grand
        }
    }

    @Synchronized fun union(x: Int, y: Int, preferRoot: Int): Int {
        val a = find(x); val b = find(y)
        if (a == b) return a
        val root = if (find(preferRoot) == a) a else b
        setParent(if (root == a) b else a, root)
        return root
    }

    @Synchronized fun newId(): Int = ...   // bump the counter, append a segment if needed
}
```

Three details that matter:

- **Path halving, not full compression**, so `find` writes at most one CAS per step and a failed CAS
  is simply ignored — another thread got there first with an equally valid link.
- **Segmented storage**, because copy-on-grow is the one thing that would break the "parent links only
  move towards a root" invariant: a `find` holding the old array could return a representative a union
  has already superseded. Appending segments never moves an existing entry.
- **`preferRoot` is a parameter, not a comparator**, which is what lets R3 pass the receiver's id
  (§3.2) without inventing a fake total order over ids.
### 3.4 Identity, and why the sentinel matters

**`anyId` participates in node identity** — `hash`, `equals`, and `AccessTreeInterner.InternStrategy`.
Without that, interning fuses structurally identical `[any]` subtrees across unrelated facts in
unrelated methods (`InternStrategy` compares children by identity and nothing else), and since the
carrier of every terminal `[any]` has the same shape, the budget would collapse into one global pot.

The node-level invariant that makes this tractable:

> **`anyId != 0` if and only if `accessors` contains `ANY_ACCESSOR_IDX`.**

It should be a `check()` in the constructor's init block. Everything below follows from it, and it
turns the whole propagation problem into a mechanical rule (§3.7).

Four things make identity participation safe here, where it was not for the superseded per-fact limit:

- **`[any]`-free nodes carry the sentinel `0`**, contribute nothing to `hash`, and compare exactly as
  today. That is the overwhelming majority of nodes, so **the feature is provably inert on trees with
  no `[any]` in them** — and with `L < 0` every node is `0`, making the analysis bit-identical to today.
- **The taint-mark check is untouched, and now provably.** `isLegalNodeBelowTaintMark` (AT:488-489)
  compares structurally (`==`, not `===`) against three singletons. A node with `anyId != 0` owns an
  `[any]` edge, hence has non-null `accessors`, hence fails `isStructurelessLeaf` and was never equal
  to a singleton anyway; and the singletons keep id `0`. So no comparison outcome changes. This is
  precisely the trap that killed identity participation for the superseded per-fact limit, where the
  limit rode on *every* node including the leaves.
- **`createElementAndField`'s singleton collapse stays valid.** AT:2251-2252 returns the shared `base`
  singleton whenever there are no accessors and no exclusion; by the invariant such a node has
  `anyId == 0`, so the collapse never loses an id. (This is also the reason not to invent "dormant"
  ids on `[any]`-less nodes: they would break this collapse and leak into every leaf.)
- **Omissions become compile errors.** In identity means a constructor parameter with no default, so
  all five private-constructor sites — `markInterned` (AT:1494) and `Serializer.readAccessNode`
  (AT:2018) included — must supply it.

**The id in `equals`/`hashCode` must be the raw stored id, never `find(id)`.** A `hashCode` that
called `find` would *change over time*: a union moves the representative, the node's hash changes, and
every hash structure already holding it — `AccessTreeInterner`'s bucket map, `EdgeSet`
(`EdgeCollection.kt:177`), `hashSetOf<FinalFactAp>()` in `MethodAnalyzerEdges.kt:47` — silently loses
it. `equals` must match `hashCode`, so it too compares raw. `find` appears only in the merge guard
(§3.5), where it decides whether to rebuild rather than what a node *is*.

Do canonicalise at construction — pass `find(id)` in, so freshly built nodes carry representatives and
the structural duplicates a union leaves behind die out as the analysis rebuilds trees, which §4.3
shows it does constantly. The distinction is: `find` at *build* time, raw at *compare* time.

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

### 3.5 An id change is a non-empty delta

The merge guards must compare the id, not only the shape:

```kotlin
// AT:1158-1165 mergeAddStep, and AT:1212-1218 mergeAddDeltaStep -- both gain the id term
if (isAbstract == this.isAbstract && isFinal == this.isFinal
    && deepExclusions == this.deepAccessorExclusion && mergedAccessors == null
    && dsu.find(mergedAnyId) == dsu.find(this.anyId)) return this
```

**Here the comparison is by representative, not raw** — the opposite of §3.4's rule for `equals`, and
for a reason that is worth being explicit about. `equals` must be stable over time because hash
structures cache it; the guard is evaluated fresh on every merge and its job is "would rebuilding
change anything real?". Comparing raw there would make a node whose representative had moved look
different from its own merge result forever, and the fixpoint would churn on a distinction with no
content. Comparing by representative also has the side effect §3.5's second bullet wants: the rebuilt
node is stored carrying the current representative, so the stale id dies.

The two identity fast paths above the guard — `if (this === other)` at AT:1237 and `if (a === b)` at
AT:1249-1253 — need no change and must not get one. The same object trivially has the same id, so
returning it with a null delta is right.

A merge that changes nothing structurally but moves the node to a different representative therefore
still produces a delta and still propagates. Two reasons that is right:

1. **A union can push the merged total over `L`.** `|A ∪ B| ≥ max(|A|, |B|)`, so facts that were
   previously free to grow may now be refused. The delta makes that visible to the fixpoint instead of
   waiting for the next incidental read.
2. **It keeps ids converging on representatives.** Without it a slot can hold a stale id indefinitely
   and every `find` pays the chain; with it the slot is rewritten with the representative, keeping
   `find` shallow on the hot path.

The extra propagation is bounded: an id changes only when a union moves its representative, and the
number of representatives only ever decreases.

Note this is the **opposite** of the rule the superseded design reached, where a limit-only change was
deliberately suppressed to avoid re-deriving work. The difference is that a budget *value* is not
identity, whereas a manager id is — a fact under a different manager is genuinely a different fact to
everything downstream.

### 3.6 Threading

Manager operations are cross-thread because `TreeApManager` is created once per phase and shared by
every unit runner on a pool of `(availableProcessors() / 2)` threads
(`TaintAnalysisUnitRunnerManager.kt:91-96`). Everything mutable already on it is explicitly safe —
`AccessorInterner` uses `synchronized(this)`, `SoftReferenceManager` uses `ConcurrentLinkedQueue` plus
`AtomicBoolean`.

The split that matters for cost: **`find` lock-free on the hot path; `union` and manager-trie mutation
synchronized and rare.** This is not what a narrower design would have needed — the two spend sites are
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
> `anyId != 0  ⟺  ANY_ACCESSOR_IDX ∈ accessors`.

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

**AT:807's union is not complete as stated.** `stripAnyBelowCoveredPath` (AT:817-845) hoists `[any]`s
found on *covered-only* paths; its `else -> node` arm leaves a subtree under an **uncovered** accessor
untouched and does not descend it. A type-info accessor is uncovered and, unlike a taint mark, may
legitimately carry children — so `T.[typeinfo].[any]ᴹ²` survives the strip, and the new `[any]ᴹ¹`
lands above it: two managers on one branch, §2.4 violated. The fix is cheap and exact, because the
walk is already there: in the `else` arm, when the child has `containsAnyInThisOrDeepNodes`, scan it
for ids and union them without stripping. Gated on the existing flag, this costs nothing on the
overwhelmingly common case. Note this also means **B1 needs no new node field** — the slow arm walks
the subtree anyway, so it can accumulate the N-way union as it goes, and the fast arm's
`!containsAnyInThisOrDeepNodes` guard is already the O(1) case split.

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
parent edge is the concrete `f`, producing `x.[any]ᴹ¹.f.[any]ᴹ².g` — two managers, one branch, §2.4
violated, and the `Lᵈ` population back. The fix rides on machinery the function already has: it
threads `path: IntArrayList` down the spine, so it can thread one more int.

```kotlin
// concatToLeafAbstractNodes gains `governingAnyId: Int`, passed at AT:1688-1691 as
//     if (accessor == ANY_ACCESSOR_IDX) this.anyId else governingAnyId
// and at the leaf (AT:1659-1669) every manager in the grafted delta is unioned into it.
```

By §2.4 there is exactly one governing manager per path, so this is one int per stack frame, not a
set. Collecting "every manager in the delta" is a subtree scan gated on
`containsAnyInThisOrDeepNodes`, and the delta is the residual of one premise match, so it is small.

This threading turns out to do more than repair the invariant, and the extra job is what makes two
other sites affordable. Several places mint a *structurally derived* fact whose `[any]` has no
predecessor to inherit from — most sharply `SummariesIdStorageNode.finalAccess`
(`MethodInitialToFinalApSummaries.kt:151-157`), which rebuilds the identity summary's exit fact from
the storage **trie key**, a premise chain that carries no manager at all. Minted in isolation such a
fact would carry a full fresh budget. But it is never *read* before it is applied, and applying it is
exactly a graft: the caller's fact supplies the delta, the threading unions the caller's real manager
into the fresh one, and a fresh manager has an empty trie, so `|∅ ∪ A| = |A|` and **no budget is
refilled**. The mint is transient by construction.

That is why §4.4 is ranked above §6.3 in the implementation order: get the threading right and the
derived-fact mints heal themselves; get it wrong and they are permanent refills on top of a broken
invariant.

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
   makes the remaining budget go further, i.e. less coarsening — but it means the trie is a
   *lower bound* on what was materialised, and §12's counters must not treat it as exact.
3. **Deserialisation is the one `[any]` that can enter a prescan-phase tree** (AT:2018 never consults
   the strategy). Since prescan installs `AnyAccessorDisabled`, whose `unrollAccessor` **throws**, a
   covered read on such a tree is a crash, not a refill. §13 R8.
4. **`FilteredNode.create` interns the delta with a *fresh* interner per `concat` call** (AT:1603).
   Two structurally identical `[any]` subtrees inside one delta become one object, and the surrounding
   caches are all `IdentityHashMap`s over those interned nodes. Any identity-keyed side table
   inherits this aliasing.

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
be the same object and the trie could not be built.

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
  `M.child(p)`, the second is free, and the trie stays one level deep no matter how wide the fan-out.
  Two materialised paths cost one accessor.
- advancing: they record `M.child(f).child(p)` and `M.child(g).child(p)`. Two paths, two accessors.
  This is the "trie of emitted paths" the design is named after, and it is the only version that
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

- `AbstractionState` carries a `governingAnyId`, initialised to `0` and set to `state.added.anyId`
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

A manager trie is insert-only, so `root.total` is monotone increasing. Union only merges tries, and
`|A ∪ B| ≥ max(|A|, |B|)`, so a union can only move a manager *closer* to the cut, never away from it.
Once `total ≥ L` no further accessor is materialised out of that `[any]`.

Therefore **at most `L` distinct concrete prefixes are ever materialised out of any one `[any]`
origin.** That is a bound on the *population*, which is what §1.2 could not deliver: the per-fact
limit bounded each chain at `L` while allowing `breadth^L` chains.

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
subset. That is why the primitive splits, and why `AnyFieldMarkExclusionTest.kt:318` is the test that
must stay green.

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

One over-count is deliberate and belongs here: a **cross-origin cascade** (§2) sets the fused
`total` to `total(Ox) + total(Oy)` rather than `|Ox ∪ Oy|`. It over-states by the size of the shared
prefix set, which refuses sooner — a precision loss in the sound direction, taken to avoid a full trie
product on a rare path. §12 counts cascades; if they turn out not to be rare, the product is the fix.

### 8.4 Determinism, honestly

Which `L` prefixes get into the trie before the cut fires depends on arrival order, so the result is
**order-sensitive in precision**. Three bounds on how much that matters:

1. **It cannot change soundness.** Every reachable trie state yields a valid over-approximation
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

§3.5 deliberately makes an id change produce a delta, and §3.4 puts the id in identity. Together these
put `anyId` inside the analysis fixpoint, and the storage layer will act on it: `mergeAdd`'s
"unchanged" test is `===` on the result (`MethodEdgesFinalTreeApSet.kt:33`,
`MethodEdgesInitialToFinalTreeApSet.kt:100`, `MethodEdgesNDInitialToFinalTreeApSet.kt:34`), and
`enqueuedUnchangedEdges` is an `ObjectOpenHashSet<Edge>` (`EdgeCollection.kt:177`) whose `Edge`
hashes its `FinalFactAp`, hence the node, hence the id. So a fact whose id moved is a **new** fact to
the worklist. That is intended — a union can push the merged total over `L` and the fixpoint has to
see it — but it has to terminate.

It does, and the argument is worth writing down rather than assuming:

- **Ids per component only ever decrease.** A union reduces the number of live representatives and
  nothing increases it. So along any one fact's history the id changes at most (number of unions on
  its component) times, each change costing one extra propagation.
- **A mint cannot be loop-carried.** The only unconditional mint is `prependAnyAccessor`'s fast arm,
  guarded by `!containsAnyInThisOrDeepNodes`. Its *output* carries an `[any]`, so re-entering the same
  site with that output takes the slow arm and reuses (R2). A cycle in the analysis therefore mints
  once and reuses thereafter, and the second lap merges to the representative, giving an empty delta.
- **The exception is destroy-then-recreate.** `clearChild(ANY_ACCESSOR_IDX)` (live at
  `Cleaner.kt:187`) and `abstractOnly` delete an `[any]` with no successor and no refund (§4.6.2). A
  cycle containing both a destruction and a re-creation mints on every lap, and each mint is a fresh
  fact. This is the one shape that can churn.

The honest position is that this last case is bounded only by the analysis's own convergence, not by
anything in this design, so it is measured rather than argued: §12 counts mints per site and mints
whose result is structurally equal to a node already seen. If that counter grows without bound on a
witness, the fix is to make the two destruction sites preserve the id for a subsequent re-creation at
the same node — which is implementable but was deliberately left out here, because it puts a
non-zero id on an `[any]`-less node and breaks the `anyId != 0 ⟺ has an [any] edge` invariant that
§3.7's whole propagation rule rests on. Do not add it speculatively.

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
| `opentaint.anyManagerDiag` | counters: managers allocated by site, unions, records, refusals, distinct managers per origin (§8.3), trie sizes at exit | `false` |

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

1. **`AnyIdDsu`** (§3.3) — dedicated, segmented, lock-free `find` with path halving, synchronized
   `union(x, y, preferRoot)` and `newId`. Standalone, nothing else depends on it.
   *Gate: single-threaded correctness (find/union/preferRoot), plus a concurrency test — N threads
   unioning and finding while a grower appends segments, asserting every `find` returns the current
   representative and never a superseded one.*
2. **`AnyUnrollManager` + `TreeApManager` ownership.** The trie, `originId`, `total` at the origin,
   the DFA-product merge with an identity-keyed memo (§2.2), the representative→manager map with
   **lazy** object allocation, the cross-origin cascade, and the mint/union entry points on
   `TreeApManager` (§2.1). Nothing reads it yet.
   *Gate: one successor per accessor after merging two overlapping tries; `total == |A ∪ B|`, not
   `|A| + |B|`; `union(X, X)` idempotent; no infinite loop on a shared sub-trie; a union drops one
   manager object; a cross-origin union fuses the origins and leaves exactly one `total`. Full suite
   green.*
3. **The id on the node.** `anyId` in identity (§3.4), the
   `anyId != 0 ⟺ ANY_ACCESSOR_IDX ∈ accessors` check in the init block, `find(id)` canonicalised at
   construction and **raw** in `hash`/`equals`/`InternStrategy`, plumbed through the five
   private-constructor sites (AT:1494, 2018, 2180, 2210, 2254), the `create` overloads and every
   `manager.create(...)` caller per §3.7. Still inert.
   *Gate: §12.7 (JOL + node counts); with `L < 0` every node is `0`, so `flags`, `hash` and every
   comparison are bit-identical to today — assert that rather than assuming it; and a unit test that
   a union does not change any live node's `hashCode`.*
4. **The lifecycle rules.** Allocate / union / propagate at every site in §4.1–§4.5. Specifically
   including, because a census found each of them missing from the first draft: the `filterStartsWith`
   spine rebuild (AT:1750) and `reconstructRemainder` (AT:721) carrying the consumed id; the
   `governingAnyId` thread through `concatToLeafAbstractNodes` (§4.4); the uncovered-accessor scan in
   `stripAnyBelowCoveredPath` (§4.1); the `bulkMergeAddAccessors` entry id (§3.7); the delta node's id
   (§3.7); the deserialisation thread (§9); and the N-way unions (§4.6.1) accounted on the
   **completed** union. Still no charge and no refusal.
   *Gate: §12.1, now two counts — distinct managers reachable from one origin must be 1, **and
   distinct managers on any single root-to-leaf path must be ≤ 1** (§2.4). This is the step that
   either works or does not; do not proceed past a failing count. The branch count is the more
   important of the two, because §8.3 shows its failure mode is `Lᵈ` rather than `kL`.*
5. **R4: record.** The covered-read record at `getChild`'s arm, plus the build/query split (§5.2) as a
   second entry point rather than a flag on the hot path. Recording only — nothing is refused yet.
   *Gate: §12.5 (query callers record zero) and §12.4 (records track the `fromAny` population). This
   is where the design is compared against the 657,633 baseline and against the prototype's 1,448.*
6. **The refusal.** `addParentAbsorbingAny` (§5.3) and the budget test at the union-find root.
   *Gate: §12.2's superset check on openmrs and tms; a new shape-asserting `filterStartsWith` test;
   `AnyFieldMarkExclusionTest.kt:318` green.*
7. **TIFA integration.** Consult the manager **before** `AccessPathTrieNode.unrollAccessors` (§6.2),
   so a refusal does not burn premise demand that a better-funded state could have served.
   *Gate: the seven cap tests in `AnyPremiseAbstractionTest`, extended for the manager.*
8. **Retire `unrolledFactCount`** (TIFA:401-408) and restore the property read at TIFA:517-518, which
   is currently hard-wired to `100`.

Steps 1–4 can land behind `L < 0` with no behavioural change at all, which makes the risky part
(5–7) a small, separately revertable surface.

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

Also count, under the same flag: unions, **cross-origin cascades** (§8.3 — the design assumes these
are rare and over-counts when they happen), lazily-allocated manager objects vs. minted ids, and
records refused.

Run all of this before any tuning. A design whose bound leaks is not worth sweeping.

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

### 12.7 Heap — gates §3.4
The `anyId` field takes `AccessNode` from 53 bytes of content / 56 aligned to 57 / **64**: **+8 bytes
per node** on the most numerous object in the analysis. Verify the size with JOL, then measure node
count and peak RSS on conductor and thingsboard at `L < 0` versus the chosen `L`.

Measure the node **count** too, not just the per-node size: putting `anyId` in identity fragments the
interner by ×(distinct origins touching a shape). The fallback if it does not fit is to drop the id
out of identity, which costs the per-origin scoping (interning fuses toward one global manager) and
is what §12.3 would then have to price. Manager objects also grow, though unions monotonically reduce
them (§13 R11).

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
| R6 | A racing `find` reads a stale parent, or CAS compression loses an update | medium | §3.3: following parents converges regardless, and `union` is synchronized; the failure mode is a slower `find`, not a wrong representative |
| R7 | N-way unions accounted incrementally instead of on the completed union, double-counting shared prefixes | medium | §4.6.1 — the trimming of §4.2 fires *inside* `stripAnyBelowCoveredPath`'s own merge loop |
| R8 | A deserialised `[any]` reaches a prescan-phase tree, where `AnyAccessorDisabled.unrollAccessor` **throws** | low but total (analysis stalls) | AT:2018 is the one `[any]` creation site that never consults the strategy; guard the coverage query. This class of bug has been hit once, stalling openmrs at `Progress: 1/7367` |
| R9 | The manager and `AccessPathTrieNode.unrollAccessors` disagree about which accessors remain, and the memo has no un-take | medium | §6.2 — consult the manager first; step 6 sequences it |
| R10 | The query/build split (§5.2) is misclassified — a build treated as a query under-charges | medium | §12.5 counts records per caller; the list is ten functions |
| R11 | Manager and trie-node allocation churn adds GC pressure on a heap-bound workload | medium | each trie is O(L), but the number of origins is not; §12.7 counts objects, not just node size |
| R12 | An `L` small enough to converge conductor is coarse enough to add FPs elsewhere | medium | §12.3 requires openmrs/tms/thingsboard SARIF-identical at the chosen `L` |
| R13 | Order-sensitivity moves findings between runs | medium | §8.4 states the cost; §12.6 measures it — and it has never been run |
| R14 | The interner data race returns a wrong accessor index, diverging findings independently of this design | **high for measurement** | the fix `e082a4b72` is **not** on this branch — land it first, or every measurement is uninterpretable |
| R15 | Records lost at the two no-refund destruction sites (§4.6.2) make the trie under-count | low | sound (the budget goes further, never shorter); §12's counters must treat `total` as a lower bound |
| R16 | `find` leaks into `hashCode`/`equals`, so a union changes a live node's hash and every hash structure holding it loses the entry | high but preventable by rule | §3.4: raw at compare time, `find` at build time and in the merge guard only; step 3's gate asserts a union changes no live `hashCode` |
| R17 | The id is inside the fixpoint (§8.5) and a destroy-then-recreate cycle mints on every lap | medium | §8.5 proves mints are not loop-carried except through that one shape; §12 counts mints per site. The obvious fix breaks §3.7's invariant — do not add it speculatively |
| R18 | `InternStrategy.equals` (`AccessTreeInterner.kt:15-29`) is a *second*, different comparison from `AccessNode.equals` and already omits `deepAccessorExclusion`; forgetting `anyId` there fuses two budgets on a hash collision | medium, silent | §3.4 names all three places that must learn about the id |
| R19 | Cross-origin cascades are not rare, so the `total(Ox) + total(Oy)` over-count coarsens broadly | medium | §12.1 counts cascades; the fallback is the full trie product |
| R20 | `anyId` adds one more per-`TreeApManager` namespace to a codebase with no `check(manager === …)` in the tree backend | low — no live path found (§9.1) | traced through `resetApManager` and `selectPhase`; add the guard the automata backend already has |

---

## 14. What this design does not do

It bounds how far an `[any]` can be *unrolled*; it does not reduce the number of `[any]`s. The ten
`$*` whole-object source markers that seed the conductor blow-up — worth 16–37× on their own — are
untouched. If `L` has to go very low to converge conductor, that is evidence the source rules are the
better lever and this bound is treating a symptom. §12.3's sweep is what tells them apart.
