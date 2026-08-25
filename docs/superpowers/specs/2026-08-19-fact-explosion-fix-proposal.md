# Fact explosion: fix proposal

Date: 2026-08-19. Branch `saloed/5-default-get` @ `4888917f0`.
Evidence base: `issue-explore.md` section "2026-08-19", JFR re-analysis, one instrumented run.

Four changes, in the order they should land. Fix 2 is the one that matters; Fix 1 is free and should
go first so its effect is separable.

---

## The asymmetry the whole proposal turns on

`TreeInitialFactAbstraction` has two entry points into the same traversal:

```kotlin
// :31-44  addAbstractedInitialFact  --  `added` changed, passes the DELTA.  Incremental.
val addedFact = facts.addInitialFact(factAp.access, interner) ?: return emptyList()
addAbstractInitialFact(facts, factAp.base, addedFact, abstractFacts, typeChecker)

// :46-70  registerNewInitialFact  --  `analyzed` changed, passes the WHOLE accumulated tree.  Not incremental.
if (!facts.addAnalyzedInitialFact(factAp.access, excludedAccessors)) return emptyList()
addAbstractInitialFact(facts, factAp.base, facts.allAddedFacts(), abstractFacts, typeChecker)
```

`registerNewInitialFact` **does not modify `added` at all** — it only writes one path into the `analyzed`
trie. Yet it re-walks the entire accumulated fact tree against the entire trie, from the root, on every
one of its ~566,000 passing calls. `allAddedFacts()` grows monotonically for the lifetime of the method
analyzer, so per-call cost grows monotonically. That is the stall.

The fix is to make it incremental **on the `analyzed` axis**, exactly as its sibling already is on the
`added` axis.

### Why this is where the time is

`abstractAccessPath` (`:170`) is an `inline` function whose emission callback is `crossinline`, so the
entire traversal loop is inlined into `addAbstractInitialFact`, and `createNodeFromReversedAp` — which
itself inlines `foldRight` — is the named frame JFR resolves inside that inlined region. The 21.03%
leaf attribution is therefore best read as *the traversal*, not as node construction. Three independent
checks agree:

- `AccessPath.AccessNode.<init>` (`AccessPath.kt:230-240`) is O(1): `hash` and `size` are derived from
  `next` in constant time. Nothing per-call is expensive.
- `AccessPath$AccessNode` does not appear in the allocation profile at all, while
  `createNodeFromReversedAp` is 21% of CPU. A method whose only job is allocating cons cells cannot be
  21% of CPU and invisible in a volume-weighted allocation profile.
- The instrumented run recorded 382,211 emissions. At O(1) per node and ~5 nodes per emission that is
  a few tens of milliseconds, not 57 seconds.

**Consequence for validation: the counter that proves or kills Fix 2 is `states visited`, not
`emissions`.** See §5.

---

## Fix 1 — `unrollAccessors`: 32.6% of all allocation, exact, ~15 lines

`AccessPathTrieNode.unrollAccessors` (`TreeInitialFactAbstraction.kt:347-354`) is the single largest
allocation site in the analyzer: **198.15 GB of `int[]` + 60.40 GB of set objects = 258.55 GB of the
792.89 GB total**. It allocates a default-capacity `IntOpenHashSet` on every call and, in steady state,
returns it empty.

Two facts make an exact guard available:

1. It has exactly **one** call site, `:189`, always of the form `T.unrollAccessors(T.exclusions())` —
   the node's own `terminals`.
2. `terminals` is created once (`:341-342`) and only ever grows (`:370` `getTerminals().addAll(...)`).

So *same set object + same size ⟹ same content ⟹ everything already unrolled ⟹ empty result*.

```diff
     class AccessPathTrieNode {
         private var children: Int2ObjectOpenHashMap<AccessPathTrieNode>? = null
         private var terminals: IntOpenHashSet? = null
         private var unrolled: IntOpenHashSet? = null
+        /** Identity + size of the set last passed to [unrollAccessors]; see the guard there. */
+        private var unrolledFrom: IntOpenHashSet? = null
+        private var unrolledFromSize: Int = -1
@@
         fun unrollAccessors(accessors: IntOpenHashSet): IntOpenHashSet {
-            val current = unrolled ?: IntOpenHashSet().also { unrolled = it }
-            val result = IntOpenHashSet()
-            accessors.forEachInt {
-                if (current.add(it)) result.add(it)
-            }
-            return result
+            // The sole call site (:189) always passes this node's own `terminals`, which is created
+            // once and only ever grows. Same object at the same size => same content => every
+            // accessor was already unrolled. The identity check makes this fail safe: a future second
+            // call site simply falls through to the full computation.
+            if (accessors === unrolledFrom && accessors.size == unrolledFromSize) return NO_ACCESSORS
+
+            val current = unrolled ?: IntOpenHashSet(accessors.size).also { unrolled = it }
+
+            var result: IntOpenHashSet? = null
+            accessors.forEachInt { accessor ->
+                if (current.add(accessor)) {
+                    (result ?: IntOpenHashSet(SMALL_SET_EXPECTED).also { result = it }).add(accessor)
+                }
+            }
+
+            unrolledFrom = accessors
+            unrolledFromSize = accessors.size
+            return result ?: NO_ACCESSORS
         }
 
         companion object {
             fun empty() = AccessPathTrieNode()
+
+            private const val SMALL_SET_EXPECTED = 4
+
+            /**
+             * Shared empty result. Safe to share because it is only ever read: the sole consumer
+             * checks `isNotEmpty()` (:190) and drops it, so it never even reaches an
+             * [AnyAccessorUnrollRequest].
+             */
+            private val NO_ACCESSORS = IntOpenHashSet(0)
```

`forEachInt` is `inline` (`util/IntCollectionUtils.kt`), so capturing `result` costs no closure.

**Why the numbers say this is the right site.** `IntOpenHashSet()` delegates to `IntOpenHashSet(16, .75f)`
= `int[33]` ≈ 152 B against a ~48 B object. **152/48 = 3.17**; measured **198.15/60.40 = 3.28**. The
arithmetic closes, which is what identifies the constructor.

**Risk: low.** Exact, single call site verified by grep, fails safe.
**Expected: removes ~33% of all allocation and most of `unrollAccessors`' 5.12% CPU.** It does not touch
the 33%/21% envelope — that is Fix 2.

---

## Fix 2 — incremental abstraction on the `analyzed` axis

### The change to `add`: report *where* the trie changed

```diff
+            /** [addWithChangeDepth] returned no modification. */
+            const val NOT_MODIFIED = -1
+
+            /**
+             * As [add], but returns the depth of the shallowest trie node whose content changed
+             * (0 == root), or [NOT_MODIFIED]. A node counts as changed if it was newly created, or —
+             * for the terminal node — if its `terminals` set was created or grew.
+             */
+            fun addWithChangeDepth(
+                initialRoot: AccessPathTrieNode,
+                initialAccess: AccessPath.AccessNode?,
+                exclusions: IntOpenHashSet,
+            ): Int {
+                var trieNode = initialRoot
+                var access = initialAccess
+                var depth = 0
+                var firstCreatedDepth = NOT_MODIFIED
+
+                while (true) {
+                    if (access == null) {
+                        var modified = trieNode.terminals == null
+                        modified = modified or trieNode.getTerminals().addAll(exclusions)
+                        if (firstCreatedDepth != NOT_MODIFIED) return firstCreatedDepth
+                        return if (modified) depth else NOT_MODIFIED
+                    }
+
+                    val children = trieNode.getChildren()
+                    var child = children.get(access.accessor)
+                    if (child == null) {
+                        child = empty()
+                        children.put(access.accessor, child)
+                        if (firstCreatedDepth == NOT_MODIFIED) firstCreatedDepth = depth + 1
+                    }
+
+                    trieNode = child
+                    access = access.next
+                    depth++
+                }
+            }
```

### The seed computation

```kotlin
/**
 * The states the full traversal would reach after consuming [depth] accessors of [path] — i.e. exactly
 * the states from which the change reported by `addWithChangeDepth` can produce a *new* emission.
 * Also drains the unroll requests the skipped prefix would have issued, so the unroll axis is
 * unaffected by seeding.
 *
 * Returns null when the prefix contains a construct this shortcut does not mirror, in which case the
 * caller must run the full traversal. Falling back is always correct, only slower.
 */
private fun collectSeedStates(
    analyzedRoot: AccessPathTrieNode,
    addedRoot: AccessTreeNode,
    path: AccessPath.AccessNode?,
    depth: Int,
    unrollRequests: MutableList<AnyAccessorUnrollRequest>,
): MutableList<AbstractionState>? {
    var states = mutableListOf(AbstractionState(analyzedRoot, addedRoot, currentAp = null))
    var access = path

    repeat(depth) {
        val accessor = (access ?: return null).accessor
        // The traversal handles these without pushing a state (:198-201, :220-223), so there is
        // nothing to resume from.
        if (accessor == FINAL_ACCESSOR_IDX || accessor.isAlwaysUnrollNext()) return null

        val expanded = expandAnyBranches(states, unrollRequests) ?: return null
        val next = mutableListOf<AbstractionState>()

        for (state in expanded) {
            // No terminals => the traversal emits and stops here (:183-186); nothing below it exists,
            // and this node's terminals are not what changed (the change is strictly deeper).
            if (state.analyzedTrieRoot.exclusions() == null) continue
            // No trie child => the traversal terminates this branch (:230-249). Along the untouched
            // prefix the child necessarily pre-exists; the guard is defensive.
            val trieChild = state.analyzedTrieRoot.child(accessor) ?: continue

            // Mirror :203-205 exactly: iterate the added node's own accessors rather than using the
            // ANY-merging `getChild`, which would resolve to a different node.
            var addedChild: AccessTreeNode? = null
            state.added.forEachAccessor { a, n -> if (a == accessor) addedChild = n }
            val child = addedChild ?: continue

            next += AbstractionState(trieChild, child, ReversedApNode(accessor, state.currentAp))
        }

        states = next
        access = access.next
    }

    return expandAnyBranches(states, unrollRequests)
}

/** Mirrors :188-196: an `<any>` branch keeps the trie node and the path, descending only `added`. */
private fun expandAnyBranches(
    states: MutableList<AbstractionState>,
    unrollRequests: MutableList<AnyAccessorUnrollRequest>,
): MutableList<AbstractionState>? {
    val result = mutableListOf<AbstractionState>()
    for (state in states) {
        var current = state
        result += current
        while (current.added.containsAnyAccessor()) {
            val exclusions = current.analyzedTrieRoot.exclusions() ?: break
            val unroll = current.analyzedTrieRoot.unrollAccessors(exclusions)
            if (unroll.isNotEmpty()) {
                unrollRequests += AnyAccessorUnrollRequest(current.currentAp, current.added, unroll)
            }
            val anyBranch = current.added.getChild(ANY_ACCESSOR_IDX) ?: return null
            current = AbstractionState(current.analyzedTrieRoot, anyBranch, current.currentAp)
            result += current
        }
    }
    return result
}
```

### Wiring

```diff
     override fun registerNewInitialFact(
         factAp: InitialFactAp,
         typeChecker: FactTypeChecker
     ): List<Pair<InitialFactAp, FinalFactAp>> {
         factAp as AccessPath
 
         val facts = initialFacts.getOrPut(factAp.base)
         ...
-        if (!facts.addAnalyzedInitialFact(factAp.access, excludedAccessors)) return emptyList()
+        val changeDepth = facts.addAnalyzedInitialFactAt(factAp.access, excludedAccessors)
+        if (changeDepth == AccessPathTrieNode.NOT_MODIFIED) return emptyList()
 
         val abstractFacts = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
-        addAbstractInitialFact(facts, factAp.base, facts.allAddedFacts(), abstractFacts, typeChecker)
+        addAbstractInitialFact(
+            facts, factAp.base, facts.allAddedFacts(), abstractFacts, typeChecker,
+            seedPath = factAp.access, seedDepth = if (INCREMENTAL) changeDepth else 0,
+        )
         return abstractFacts
     }
```

```diff
     private fun addAbstractInitialFact(
         facts: MethodSameBaseInitialFact,
         concreteFactBase: AccessPathBase,
         initialConcreteFact: AccessTreeNode,
         abstractFacts: MutableList<Pair<InitialFactAp, FinalFactAp>>,
-        typeChecker: FactTypeChecker
+        typeChecker: FactTypeChecker,
+        seedPath: AccessPath.AccessNode? = null,
+        seedDepth: Int = 0,
     ) {
         var concreteFactAccess = initialConcreteFact
+        var pendingSeedDepth = seedDepth
         while (true) {
             val unrollRequests = mutableListOf<AnyAccessorUnrollRequest>()
-            abstractAccessPath(facts.analyzed, concreteFactAccess, unrollRequests) { abstractAccess ->
+            val seeds = if (pendingSeedDepth <= 0) null else
+                collectSeedStates(facts.analyzed, concreteFactAccess, seedPath, pendingSeedDepth, unrollRequests)
+
+            abstractAccessPath(facts.analyzed, concreteFactAccess, seeds, unrollRequests) { abstractAccess ->
                 ...
             }
 
+            // Later rounds already operate on a delta from `addInitialFact`, so they traverse it whole.
+            pendingSeedDepth = 0
             concreteFactAccess = facts.unrollAnyAccessors(unrollRequests, typeChecker) ?: break
         }
     }
```

and `abstractAccessPath` takes `seedStates: MutableList<AbstractionState>?`, using it as the initial
worklist when non-null and the single root state otherwise.

### Soundness

> **Theorem.** Let the trie be modified by `addWithChangeDepth(path, ΔE)` returning depth `d`. Every
> abstract AP that a full traversal emits after the modification, and did not emit before it, is also
> emitted by the traversal seeded at the states at depth `d` along `path`.

**Proof.** The traversal's action at a state `(T, A, q)` is a function of `T.terminals`, `T.children`
and `A`. `add` modifies only (i) `children` of the node at depth `d-1`, by one entry, for the accessor
`a_d`; (ii) nodes at depth ≥ `d`, every one of which is newly created; (iii) `terminals` of the node at
depth `k = |path|`, where `k ≥ d`. `added` is not modified at all.

For any state whose path is not an extension of `path[0..d]`, both `T` and `A` are unchanged, so its
action is unchanged, and by induction on the descent the set of states it generates is unchanged —
hence its emissions are unchanged. At depth `d-1` the sole change is that accessor `a_d` now descends
instead of terminating: that *removes* at most one emission and *adds* the descent into depth `d`.
Therefore every new emission originates at a state at depth `d` along `path`, or below one. The seed
set is by construction exactly the states at depth `d`, so the seeded traversal generates precisely
those states and their descendants. ∎

Two things the theorem deliberately does **not** claim, both fine:

- The seeded traversal may emit **fewer** APs than a full one — namely the ones the full traversal
  would re-emit. Re-emissions are deduped downstream by `MethodAnalyzerEdges.addTaintedFactEdge`
  (returns `emptyList()` for a present edge), and were **measured at 0.03%** (126 duplicates against
  382,211 emissions, constant while emissions grew 31×).
- It says nothing about unroll requests. Those are handled separately: `collectSeedStates` drains the
  skipped prefix's requests itself, so the unroll axis is bit-identical to the full traversal.

### Fallbacks, all correct-by-construction

`collectSeedStates` returns null — meaning "run the full traversal" — on: an `isAlwaysUnrollNext`
accessor in the prefix, a `FINAL_ACCESSOR_IDX` in the prefix, a missing ANY branch, and a shorter path
than the requested depth. A null return is never wrong, only slower.

### Flag

`private val INCREMENTAL = System.getProperty("opentaint.incrementalAbstraction") != "false"` so the
change can be A/B'd against itself in one build, and disabled in the field without a revert.

### Expected effect and risk

Per-call cost falls from O(added-nodes within trie depth) to O(added-nodes below the change). The
premises that drive this workload are deep (`arg(0).descriptor.fields.content.right.right`), so the
seeded subtree should be a small fraction of the whole. **Risk: medium** — this is subtle code. That is
what §5's differential mode is for.

---

## Fix 3 — carrier slots are not unroll candidates (the semantic fix; needs a decision)

The regression's true cause is the `<rule-storage>` → semantic-name rename, which turned 343
non-unrollable carrier slots into ordinary unrollable fields (375 → 786, reproduced exactly at
`8f5299af2~1` and HEAD). Because the no-repeat-field invariant is the only terminator for field-path
growth, max path length = number of distinct unrollable field accessors — so the rename **doubled the
implicit depth bound**, which is why the blow-up is super-linear rather than 2×.

The marker was deleted from the data, but it is re-derivable: a carrier slot is one whose named field
does not resolve on its declaring class. Measured over the resolvable JDK/javax subset, **71% of
distinct slots (56% occurrence-weighted) are virtual**, including all the dominant ones
(`java.lang.Iterable#Element` 1,712, `java.util.Map#MapValue` 870, `#MapKey` 836).

```kotlin
override val unrollStrategy: AnyAccessorUnrollStrategy = object : AnyAccessorUnrollStrategy {
    private val virtualSlot = ConcurrentHashMap<FieldAccessor, Boolean>()

    private fun isVirtualSlot(accessor: FieldAccessor): Boolean =
        virtualSlot.computeIfAbsent(accessor) {
            val cls = cp.findClassOrNull(it.className) ?: return@computeIfAbsent false
            cls.findFieldOrNull(it.fieldName) == null
        }

    override fun unrollAccessor(accessor: Accessor): Boolean = when (accessor) {
        is FieldAccessor -> !isVirtualSlot(accessor)
        is ElementAccessor -> true
        else -> false   // spell out the existing arms
    }
}
```

**This must not be merged on the strength of the perf argument alone.** Excluding every virtual slot
leaves ~228 unrollable against `main`'s 375, i.e. it is *stricter than main* — `java.lang.Iterable#Element`
was never a `<rule-storage>` slot and unrolls on `main` today. The gate is a **SARIF diff against `main`
over the full ruleset**; if findings are lost, the container carriers need an explicit allow-list.

Do not attempt to type-filter instead: `fieldType = java.lang.Object` is deliberate (`3951e7228`,
1,867 positions) precisely because a concrete type can fail the read-out check and silently drop taint,
and for a genuine virtual carrier `Object` is *correct*. Tightening the filter cannot reach 56% of
occurrences.

### Two constraints that rule out the obvious alternatives

- **A depth cap at the unroll site is unsound.** `TreeApManager.kt:50-51` defines
  `isCoveredByAny(accessor) = unrollStrategy.unrollAccessor(accessor)`. `contains` returning true is a
  subsumption claim, justified only if unroll materialises the path. Rejecting a *possible* path there
  leaves `contains` still claiming coverage → false negative. The existing type filter is sound only
  because it rejects type-*impossible* paths.
- **The classical "k-limiting is a sound widening" argument does not hold here.** Premises are a
  partition carved by exclusion sets, not a refinement chain: `abstractAccessPath` (`:240-249`) emits
  `p.a/*` *because* a fact at `p` excludes `a`, and `AccessNode.filter` (`AccessTree.kt:646-663`)
  deletes excluded children. Dropping a deep premise leaves its region covered by nothing. Relatedly
  `x.<any>/*` is not sticky — `concatToLeafAbstractNodes:1314` rebuilds with `isAbstract = false` — so
  collapse-to-wildcard is unavailable.

---

## Fix 4 — two small exact changes

**4a. `ExclusionSet.Concrete.union` recomputes its hash in O(n) — 0.59% of CPU**, more than the entire
storage layer. The class maintains `hash` incrementally everywhere else (`add` at `:59`, `subtract` at
`:89`), the invariant being "hash == sum of member hashCodes"; `union` alone discards it. In the fold at
`MethodAnalyzer.kt:843` this makes a k-way union O(k²).

```diff
             is Concrete -> {
                 val union = set.addAll(other.set)
-                if (union === set) this else Concrete(union, union.hashCode())
+                if (union === set) {
+                    this
+                } else {
+                    // hash is the sum of member hashCodes (cf. add/subtract), so maintain it in
+                    // O(|other.set|) rather than recomputing over the union.
+                    var unionHash = hash
+                    for (accessor in other.set) if (accessor !in set) unionHash += accessor.hashCode()
+                    Concrete(union, unionHash)
+                }
             }
```

**4b. `InternStrategy.equals` omits `deepAccessorExclusion` — a latent soundness bug.**
`AccessNode.equals` (`AccessTree.kt:332`) compares it; the interner relies on `hash` to separate them,
but `hash` folds it in additively through a **32-bit** `hashCode`. Two structurally identical nodes whose
exclusions collide in 32 bits get silently unified.

```diff
             if (a.isAbstract != b.isAbstract || a.isFinal != b.isFinal) return false
+            // `hash` folds deepAccessorExclusion through a 32-bit hashCode and so cannot separate
+            // colliding exclusions. AccessNode.equals compares it; the interner must too.
+            if (a.deepAccessorExclusion != b.deepAccessorExclusion) return false
```

Do **not** also mix `accessors` into `AccessNode.hash` as a performance change: `InternStrategy.equals`
is 9 samples of 38,791 (0.02%), and node construction (0.58%) outnumbers interning (0.38%), so it is
plausibly net-negative.

---

## 5. Validation

**The counter that decides Fix 2 is states visited, not emissions.** Add to the traversal loop, behind
the existing diagnostics flag: number of `AbstractionState`s popped, and number of inner
`abstractAccessPath` calls, both per entry point. Compare seeded vs full on the same workload. Fix 2 is
worth shipping iff states-visited falls by a large factor; emissions should stay nearly equal.

**Differential mode.** Behind `-Dopentaint.abstractionDifferential=true`, run *both* the seeded and the
full traversal on every `registerNewInitialFact` and assert `seeded ⊆ full` and that every element of
`full \ seeded` is already present in the `analyzed` trie (i.e. was previously emitted). This turns the
soundness theorem into a runtime check and is the cheapest way to gain confidence in subtle code.

**Order of work.**
1. Fix 1 alone → re-take JFR → confirm `unrollAccessors` leaves the top allocation sites. Unambiguous,
   needs no wall-clock budget.
2. Add the states-visited counter → one run → get the ratio Fix 2 is predicted to move.
3. Fix 2 behind its flag, differential mode on → full IFDS test suites → then A/B on ThingsBoard.
4. Fix 3 only after a SARIF diff against `main` over the full ruleset.
5. Fix 4a/4b any time; independent.

**Correctness bar.** Fixes 1, 2, 4a are claimed behaviour-preserving: any change in reported findings is
a bug, not a trade-off. Fix 3 is explicitly a semantic change and is gated on the finding diff.

**Benchmarking caveat.** The box was contended by three foreign 16 GB analyzers during the instrumented
run, so no wall-clock number from it is usable. Ratios (duplicate rate, states visited) are
load-insensitive; timings are not, and need the quiet-gate harness in
`opentaint-w3-benchmark-results/post-rebase/run-matrix.sh`.

---

# Addendum (2026-08-19, after implementation): two errors in the Fix 2 theorem

Fix 2 landed as `22d59f105`. The differential mode caught **two soundness bugs in the theorem stated
above** before anything shipped. Both are places where the theorem assumed something false about the code.

## Error 1 — "no terminals ⇒ safe to skip" is wrong

The seed computation above skips a prefix node whose `exclusions()` is null, on the reasoning that
"the traversal emits and stops here, and this node's terminals are not what changed".

That is unsound. Every emission **registers itself back into the trie** via `addAnalyzedInitialFact`,
which *creates* `terminals`. So `terminals == null` ⟺ **nothing was ever emitted at that node**, and
the emission being skipped is a first-time fact, not a repeat. Now handled as a fallback
(`seedFallbackNoTerminals`).

## Error 2 — the theorem assumes a fixed trie; the traversal mutates the trie it is walking

The proof argues over `add`'s modifications alone. But the traversal itself writes to `analyzed` as it
emits, creating `terminals` at nodes it has already passed and will not revisit. Today a *later full
traversal* is what descends past those nodes — which is exactly the work seeding removes.

Counterexample found by the differential run:

```
register arg(0)/*{b}; add arg(0).b.c.d.f; register arg(0).b.c.d{f}; add arg(0).b.c.e.f;
register arg(0).b.c.e{f}
  ABSDIFF VIOLATION base=arg(0) registered=.b.c.e changeDepth=3 seeded=1 full=2
    fullOnlyAndNotYetRegistered=.b.c.d.f
```

Fixed by recording emission-made trie changes as *pending* and seeding from them on the next traversal
alongside the registered path (capped at 64, then fall back). This mechanism is **not** in the design
above and is the one substantive addition.

## Validation actually achieved

- **0 differential violations over 78,689 in-analyzer comparisons** at `registerPassed = 712,481`.
- 400-case randomised fuzz (30-op histories, seeded vs full in one JVM).
- 201 tests pass; `TreeNonIncrementalInitialFactAbstractionTest` replays the whole shared contract with
  `incrementalAbstraction = false`.
- Fallback rate **0.5%** (402 of 78,919 seedable calls), dominated by `unrollNext=344`; zero for the two
  reasons that would have indicated a structural problem.

## Reading the change-depth data correctly

Cumulative over a run, change depth 0 accounts for **78.8%** of register-traversal states, which reads
as a 21% ceiling. That is the wrong reading: the distribution is strongly non-stationary. Over the last
sampling interval (98,645 new states):

| depth | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|---:|---:|
| new states | **+24** | +129 | +62 | +9,203 | **+88,992** | +235 |

**99.98% of marginal work is at depth ≥ 1, and 90% at depth 4.** Depth-0 mass is front-loaded cheap
early calls (1.7 states/call); the tail that produces the 1,899-states-per-call explosion is deep-path
registration (depth 4: 20.7 states/call and climbing). Judge the fix on `statesByChangeDepth` marginals,
not cumulative totals.

## Remaining headroom (not implemented)

Depth-0 `terminals` growth is a **node-local** change, not a subtree change: when a node's exclusion set
grows by ΔE with no node created, behaviour changes only for accessors in ΔE that have no trie child —
the descent into existing children is provably unchanged. New emissions are then
`O(|ANY chain| × |added accessors|)` at that one node with **no descent**. This needs
`addWithChangeDepth` to distinguish "terminals created" from "terminals grew", and is a separate seeding
source that composes with the current one.

## Smaller corrections to the design above

- The spec's final `expandAnyBranches` on the return value is redundant **and harmful** — depth-`d`
  states are pushed onto the worklist and the traversal expands their ANY chains itself; pre-expanding
  re-expands each chain suffix, giving O(n²) states and duplicate emissions. Intermediate levels *do*
  need it, since those states are never pushed and their unroll requests must be drained manually.
- The separate `FINAL_ACCESSOR_IDX` guard is redundant: `isAlwaysUnrollNext()` already covers it.
- `abstractAccessPath`'s `exclusions == null` branch is dead code — the inner overload is only reached
  after `currentLevelExclusions != null` on the same node, and `terminals` only grows.
- The spec's `trieChild ?: continue` would drop an emission (the inner function emits from the exclusion
  set when the child is missing); fall back instead.
