package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.util.ConcurrentReadSafeInt2ObjectMap
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicLong

/**
 * The budget pot shared by every `[any]` position descended from one origin.
 *
 * One dag per `[any]` ORIGIN -- the point where an `[any]` edge was created with no predecessor to
 * inherit from. Every state reachable from that origin spends [total] from here, which is what makes
 * the bound a POPULATION bound rather than a per-derivation one: a budget that forks with the
 * derivation bounds the length of each chain while letting the number of chains grow like
 * `breadth^L`.
 *
 * Dags are themselves union-find nodes ([parent]): when two automata have to be fused their pots
 * combine. [rootState] is the only thing the dag has to retain about its automaton, and it exists
 * solely so a fusion can reach the two start states to merge them.
 */
class AnyUnrollDag(@JvmField val id: Int) {
    /** DSU link; `null` means this dag is a representative. Written only under the manager lock. */
    @Volatile
    @JvmField
    var parent: AnyUnrollDag? = null

    /** The pot. Monotone: transitions are added and never removed, so this only ever grows. */
    @JvmField
    var total: Int = 0

    /** Diagnostics only: reads this pot refused after it was spent. Written under the manager lock. */
    @JvmField
    var refusals: Int = 0

    /**
     * The automaton's start state, needed only to fuse two automata into one.
     *
     * Closes a reference cycle (dag -> root state -> dag) that the collector handles without help.
     */
    @JvmField
    var rootState: AnyUnrollState? = null

    override fun toString(): String = "dag#$id(total=$total)"
}

/**
 * One position in the deterministic automaton of concrete accessor sequences materialised out of an
 * `[any]`.
 *
 * The structure is NOT a trie and not even a DAG -- it must be allowed to become cyclic. A program
 * loop `while (*) { x = x.a }` over a fact `x.[any].*` produces `union(m, m.a)`, which writes
 * `m --a--> m`; that self-loop is exactly how the loop reaches its fixed point, because the next read
 * of `a` at `m` finds an existing transition, mints nothing and charges nothing. Refusing to create
 * it would produce a fresh state every lap and the analysis would never converge.
 *
 * Consequently NOTHING may compute a quantity by traversing the automaton: on a cycle the accepted
 * language is infinite. [pathCount] is maintained incrementally at the point of change instead.
 */
class AnyUnrollState(
    /** Dense, from an [AtomicInteger]; used for hashing only, never for identity or lookup. */
    @JvmField val id: Int,
    /** Strong reference to the pot this state spends from. */
    @JvmField val dag: AnyUnrollDag,
) {
    /**
     * DSU link; `null` means this state is a representative.
     *
     * Written by [AnyUnrollManager.union] (which only ever writes to a root, under the lock) and by
     * [find]'s path halving (which only ever writes to a non-root whose parent is also a non-root).
     * The two write sets are disjoint, which is what lets halving stay lock-free with a plain
     * volatile write and no CAS.
     */
    @Volatile
    @JvmField
    var parent: AnyUnrollState? = null

    /**
     * How many distinct accessor sequences reach this state.
     *
     * A state can be reached by more than one sequence -- that is what a union does, and it is the
     * whole reason the structure is an automaton rather than a trie. Charging 1 for a new transition
     * out of a shared state would under-report the population by the sharing factor, compounding
     * with every merge, so the charge is `pathCount` (see [AnyUnrollManager.readChild]).
     *
     * Maintained incrementally and saturating; never recomputed by traversal.
     */
    @JvmField
    var pathCount: Int = 1

    /**
     * The transitions out of this state: at most one successor per accessor, which is what keeps the
     * structure deterministic and re-derivation free.
     *
     * Lock-free to read ([ConcurrentReadSafeInt2ObjectMap] captures the backing arrays and retries),
     * written only under the manager lock.
     */
    @Volatile
    @JvmField
    var children: ConcurrentReadSafeInt2ObjectMap<AnyUnrollState>? = null

    /**
     * The representative of this state's DSU class, with path halving.
     *
     * Lock-free and best-effort: a lost halving write is harmless because both racing writers install
     * a link to a genuine ancestor, and ancestors are permanent (a root may acquire a parent, but a
     * non-root never leaves its tree). A stale read costs one extra hop, never a wrong answer.
     */
    fun find(): AnyUnrollState {
        var cur = this
        while (true) {
            val up = cur.parent ?: return cur
            val grand = up.parent ?: return up
            cur.parent = grand
            cur = grand
        }
    }

    override fun toString(): String = "any#$id"
}

/** Same contract as [AnyUnrollState.find], for the dag layer. */
fun AnyUnrollDag.find(): AnyUnrollDag {
    var cur = this
    while (true) {
        val up = cur.parent ?: return cur
        val grand = up.parent ?: return up
        cur.parent = grand
        cur = grand
    }
}

/**
 * Process-wide counters for the `[any]` unroll manager, enabled by `-Dopentaint.anyManagerDiag=true`.
 *
 * Every counter is incremented at the event, so nothing has to enumerate states or facts to report
 * them -- which is deliberate: a registry of states is the one thing that would force weak references
 * back into the design.
 */
object AnyUnrollDiagnostics {
    val enabled: Boolean = System.getProperty("opentaint.anyManagerDiag")?.trim().toBoolean()

    val mints = AtomicLong()
    val mintsBySite = Array(AnyUnrollManager.MINT_SITE_COUNT) { AtomicLong() }
    val unions = AtomicLong()
    val dagFusions = AtomicLong()
    val transitionsCreated = AtomicLong()
    val reads = AtomicLong()
    val readsReusedFree = AtomicLong()
    val readsRefused = AtomicLong()
    val absorptions = AtomicLong()
    val collapses = AtomicLong()

    /**
     * Facts materialised by the initial-fact abstraction's unroll -- one per `accountUnrolledFact()`
     * in the retired per-`(entry point, base)` counter.
     *
     * It exists to measure the gap between what that counter charged and what the manager charges.
     * The old counter charged once per materialised FACT, at every position, every time; the manager
     * charges once per distinct `(state, accessor)` TRANSITION, and re-deriving a recorded path is
     * free by design. Those two coincide only when paths are not re-derived at many positions, so
     * the ratio is the honest measure of how much weaker the new cut is per unit of work.
     */
    val tifaUnrolledFacts = AtomicLong()

    /**
     * The largest `total` any pot ever reached, and how many reads the single worst pot refused.
     *
     * The aggregate counters cannot tell "every pot is at its limit" from "one giant pot is at its
     * limit and refuses half the program", and those two call for opposite responses: the first says
     * the limit is too low, the second says the cut is landing on one origin and the lever is that
     * origin rather than its budget.
     */
    val maxPotTotal = AtomicLong()
    val maxPotRefusals = AtomicLong()

    fun recordPot(total: Int) {
        var cur = maxPotTotal.get()
        while (total > cur && !maxPotTotal.compareAndSet(cur, total.toLong())) cur = maxPotTotal.get()
    }

    /** §12.1: the union-without-collapse arm, broken down by the accessor that separates the two. */
    val unionWithoutCollapseMark = AtomicLong()
    val unionWithoutCollapseStatic = AtomicLong()
    val unionWithoutCollapseTypeInfo = AtomicLong()
    val unionWithoutCollapseOther = AtomicLong()

    /**
     * §12.5: reads taken through the QUERY entry point.
     *
     * It counts CALLS, not records -- a query never records, by construction, so a "must stay at
     * zero" reading of it is permanently red and meaningless. What it is actually for is spotting a
     * caller misclassified the other way: a build treated as a query under-charges, and a large
     * `queryReads` against a small `reads` is what that looks like.
     */
    val queryReads = AtomicLong()

    fun report(): String = buildString {
        append("anyUnroll ")
        append("mints=").append(mints.get())
        append(" mintsBySite=").append(
            AnyUnrollManager.MINT_SITE_NAMES.withIndex()
                .joinToString(",") { (i, n) -> "$n:${mintsBySite[i].get()}" }
        )
        append(" unions=").append(unions.get())
        append(" dagFusions=").append(dagFusions.get())
        append(" transitions=").append(transitionsCreated.get())
        append(" reads=").append(reads.get())
        append(" reusedFree=").append(readsReusedFree.get())
        append(" refused=").append(readsRefused.get())
        append(" absorptions=").append(absorptions.get())
        append(" collapses=").append(collapses.get())
        append(" tifaFacts=").append(tifaUnrolledFacts.get())
        append(" maxPotTotal=").append(maxPotTotal.get())
        append(" maxPotRefusals=").append(maxPotRefusals.get())
        append(" unionNoCollapse=[mark:").append(unionWithoutCollapseMark.get())
        append(",static:").append(unionWithoutCollapseStatic.get())
        append(",typeInfo:").append(unionWithoutCollapseTypeInfo.get())
        append(",other:").append(unionWithoutCollapseOther.get())
        append("]")
        append(" queryReads=").append(queryReads.get())
    }
}

/**
 * Allocation, union and charging for the `[any]` unroll automata. One per [TreeApManager].
 *
 * Ownership lives here rather than on the nodes because [TreeApManager] is the single object every
 * tree-backend site already holds, and it is the only common ancestor of the two spend sites, which
 * live under different owners (the abstraction under the callee's analyzer, the subscription under
 * the caller's).
 *
 * ## Threading
 *
 * `find` is lock-free on the hot path; every MUTATION -- a union, a new transition, a charge -- runs
 * inside [lock]. That is not a performance choice: two threads racing `union(x, y)` and `union(y, x)`
 * can each observe two distinct roots and write `a.parent = b` and `b.parent = a`, leaving a CYCLE in
 * the DSU forest that nothing detects and that makes every subsequent `find` spin forever. A root
 * discovered under the lock is still a root when it is written, which is what keeps the forest
 * acyclic. Halving stays lock-free because its write set (non-roots whose parent is also a non-root)
 * is disjoint from union's (roots only).
 */
class AnyUnrollManager(
    /** `L`. Negative means the feature is off: no states, no records, no refusals. */
    @JvmField val limit: Int,
) {
    val enabled: Boolean get() = limit >= 0

    private val lock = Any()
    private val stateIds = AtomicInteger()
    private val dagIds = AtomicInteger()

    /** `pathCount` saturates here: past `L` the state refuses everything anyway. */
    private val pathCountCeiling: Int = if (limit <= 0) 1 else limit

    /** R1: a fresh origin -- a new dag with `total = 0` and its root state with `pathCount = 1`. */
    fun newOrigin(site: Int): AnyUnrollState? {
        if (!enabled) return null

        val dag = AnyUnrollDag(dagIds.incrementAndGet())
        val root = AnyUnrollState(stateIds.incrementAndGet(), dag)
        dag.rootState = root

        if (AnyUnrollDiagnostics.enabled) {
            AnyUnrollDiagnostics.mints.incrementAndGet()
            AnyUnrollDiagnostics.mintsBySite[site].incrementAndGet()
        }

        return root
    }

    /**
     * R2/R3: make [a] and [b] one manager, preferring [a]'s representative.
     *
     * Receiver preference is semantically neutral -- the union merges the two states by product, so
     * the content is identical whichever survives -- but it is not neutral for speed. In `mergeAdd`
     * the receiver is the accumulated, long-lived tree, so keeping its representative means the
     * stored node's id does not change, the merge guard's `===` fires on the SAME round, and the fact
     * stays out of the worklist. Preferring the arrival would cost an extra fixpoint lap for every
     * folded loop in the program.
     */
    fun union(a: AnyUnrollState?, b: AnyUnrollState?): AnyUnrollState? {
        if (!enabled) return null
        if (a == null) return b
        if (b == null) return a
        if (a === b) return a

        // Lock-free, and it carries the steady state. Receiver preference keeps the accumulated
        // tree's STORED reference unchanged while the arrival's is absorbed, and node identity
        // compares stored references -- so "two distinct objects with the same representative" is
        // the normal case, not the exception. Without this every merge of two `[any]`-carrying nodes
        // would take the per-manager monitor on the hottest path in the analyzer just to discover
        // there is nothing to do. The DSU only ever moves towards a root, so a stale negative simply
        // falls through to the locked path.
        val fastA = a.find()
        val fastB = b.find()
        if (fastA === fastB) return fastA

        synchronized(lock) {
            var x = a.find()
            var y = b.find()
            if (x === y) return x

            if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.unions.incrementAndGet()

            val dx = x.dag.find()
            val dy = y.dag.find()
            if (dx !== dy) {
                // Two automata in, one automaton out: the pots combine and the START states merge,
                // so the result is a single deterministic structure rather than two sharing a pot.
                // Summing over-states by the sequences the two had in common, which refuses sooner
                // -- the sound direction -- and avoids a full product traversal on a rare path.
                val dyRoot = dy.rootState
                dy.parent = dx
                dx.total = satAdd(dx.total, dy.total, Int.MAX_VALUE)

                if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.dagFusions.incrementAndGet()

                val dxRoot = dx.rootState
                if (dxRoot != null && dyRoot != null) {
                    // accumulatePaths = FALSE. Both start states denote the EMPTY sequence, so
                    // merging them leaves one state reached by one sequence, not two -- and the same
                    // holds all the way down the cascade, which pairs states reached by the SAME
                    // accessor sequence in the two automata. The merged path set is the union of two
                    // sets that overlap by construction, so `max` is the right operator and `sum`
                    // over-states it by the whole overlap.
                    //
                    // Measured, before this was fixed: 11,482 of 11,625 unions on thingsboard were
                    // cross-dag fusions, so root path counts saturated at `L` and a component of a
                    // hundred fused origins refused on its FIRST new accessor. 1,323 transitions
                    // across ~690 pots -- under two each -- produced 16,792 refusals at L = 100.
                    mergeStates(dxRoot.find(), dyRoot.find(), accumulatePaths = false)
                }

                // The fusion may already have merged x and y transitively.
                x = a.find()
                y = b.find()
                if (x === y) return x
            }

            // A same-dag union DOES accumulate: `x` and `y` are different positions in one
            // automaton, so the sequences reaching them are genuinely different sequences, and one
            // new transition out of the merged state authorises all of them.
            return mergeStates(x, y, accumulatePaths = true)
        }
    }

    /**
     * The product merge. Both operands must be representatives of the SAME dag.
     *
     * The union is performed IN PLACE, which is why no separate `memo[(x, y)]` is needed to break
     * cycles: `y.parent = x` is itself the memo, and re-encountering the pair short-circuits on
     * `find(x) === find(y)`. Each productive union reduces the number of live representatives by
     * one, so the loop terminates on a cyclic structure for the same reason a memoised product does.
     *
     * The invariant that makes the lock-free read correct: **only a representative carries
     * transitions**. A state that loses root status has its child map folded into the winner in the
     * same step, so a reader that resolves `find()` and reads that state's `children` never lands on
     * an orphaned map. A reader racing the fold sees the transition missing, falls to the slow path,
     * takes the lock -- which the fold holds -- and re-resolves.
     */
    private fun mergeStates(
        x0: AnyUnrollState,
        y0: AnyUnrollState,
        accumulatePaths: Boolean,
    ): AnyUnrollState {
        val pending = ArrayDeque<AnyUnrollState>()
        pending.addLast(x0)
        pending.addLast(y0)

        while (pending.isNotEmpty()) {
            val x = pending.removeFirst().find()
            val y = pending.removeFirst().find()
            if (x === y) continue

            y.parent = x
            x.pathCount = if (accumulatePaths) {
                satAdd(x.pathCount, y.pathCount, pathCountCeiling)
            } else {
                maxOf(x.pathCount, y.pathCount)
            }

            val absorbed = y.children ?: continue
            y.children = null

            // `x` is still a root here (nothing above has repointed it), but it may stop being one
            // later in this same loop -- at which point ITS children are folded into the new winner
            // by exactly this code. So writing here is safe.
            val keys = absorbed.keys.toIntArray()
            for (accessor in keys) {
                val target = absorbed.get(accessor) ?: continue
                val existing = x.children?.get(accessor)
                if (existing == null) {
                    // One successor per accessor: an NFA here would make every lookup explore a SET
                    // of states, re-derivation would stop being free, and the whole design collapses.
                    putTransition(x, accessor, target.find())
                } else {
                    pending.addLast(existing)
                    pending.addLast(target)
                }
            }
        }

        return x0.find()
    }

    private fun putTransition(state: AnyUnrollState, accessor: AccessorIdx, target: AnyUnrollState) {
        val existing = state.children
        if (existing != null) {
            existing.put(accessor, target)
            return
        }
        val map = ConcurrentReadSafeInt2ObjectMap<AnyUnrollState>()
        map.put(accessor, target)
        state.children = map
    }

    /**
     * R4/R5: an accessor is read THROUGH an `[any]` whose position is [state].
     *
     * If the transition already exists it is reused FREE -- that is not an optimisation, it is the
     * termination argument. Otherwise a successor is minted and `pathCount` is charged to the pot.
     *
     * Returns `null` when the pot is exhausted, which the caller turns into an ABSORPTION rather than
     * a truncation (see `AccessNode.addParentAbsorbingAny`).
     */
    fun readChild(state: AnyUnrollState?, accessor: AccessorIdx): AnyUnrollState? {
        if (!enabled || state == null) return state

        if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.reads.incrementAndGet()

        // Fast path: the transition already exists. Lock-free, allocation-free, and by far the
        // common case -- which is the whole reason the automaton exists.
        state.find().children?.get(accessor)?.let {
            if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.readsReusedFree.incrementAndGet()
            return it.find()
        }

        synchronized(lock) {
            val current = state.find()
            current.children?.get(accessor)?.let {
                if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.readsReusedFree.incrementAndGet()
                return it.find()
            }

            val dag = current.dag.find()
            if (dag.total >= limit) {
                if (AnyUnrollDiagnostics.enabled) {
                    AnyUnrollDiagnostics.readsRefused.incrementAndGet()
                    dag.refusals++
                    AnyUnrollDiagnostics.maxPotRefusals.updateAndGet { maxOf(it, dag.refusals.toLong()) }
                }
                return null
            }

            val child = AnyUnrollState(stateIds.incrementAndGet(), dag)
            child.pathCount = current.pathCount
            putTransition(current, accessor, child)
            dag.total = satAdd(dag.total, current.pathCount, Int.MAX_VALUE)
            if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.recordPot(dag.total)

            if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.transitionsCreated.incrementAndGet()

            return child
        }
    }

    /**
     * The query counterpart of [readChild]: reuse an existing transition, otherwise stay put. Never
     * mints, never charges, never refuses -- a caller that only answers a boolean must not move the
     * budget (§5.2), and misclassifying a query as a build would trip the cut early and coarsen facts
     * that were never growing.
     */
    fun peekChild(state: AnyUnrollState?, accessor: AccessorIdx): AnyUnrollState? {
        if (!enabled || state == null) return state
        if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.queryReads.incrementAndGet()
        return state.find().children?.get(accessor)?.find() ?: state
    }

    /** Whether the pot behind [state] is spent, i.e. whether an accessor may still be written above it. */
    fun budgetExhausted(state: AnyUnrollState?): Boolean {
        if (!enabled || state == null) return false
        return state.find().dag.find().total >= limit
    }

    /** For tests and diagnostics only. */
    fun totalOf(state: AnyUnrollState): Int = state.find().dag.find().total

    private fun satAdd(a: Int, b: Int, ceiling: Int): Int {
        val sum = a.toLong() + b.toLong()
        return if (sum >= ceiling) ceiling else sum.toInt()
    }

    companion object {
        const val ANY_UNROLL_LIMIT_PROPERTY = "opentaint.anyUnrollLimit"

        /**
         * `-Dopentaint.anyUnrollLimit=<n>`: `L`, the per-origin budget.
         *
         * `n < 0` -- the default -- means the manager is off entirely: no state is allocated, no
         * `AccessNode` carries an id, nothing is recorded and nothing is refused, so the analysis is
         * bit-identical to one built without the feature. A non-negative `n` lets each `[any]` ORIGIN
         * materialise a path-weighted total of `n` concrete accessors before it starts absorbing
         * further steps instead of writing them.
         *
         * Read once, at class initialisation: it is consulted per covered read.
         */
        val DEFAULT_ANY_UNROLL_LIMIT: Int =
            System.getProperty(ANY_UNROLL_LIMIT_PROPERTY)?.trim()?.toIntOrNull() ?: -1

        // Mint sites, for §12.1(a): "distinct managers per origin, BY ALLOCATING SITE". The count
        // alone does not say which site leaked.
        const val MINT_PREPEND = 0
        const val MINT_DESERIALIZE = 1

        /**
         * The raw single-edge `create`, shared by the `filterStartsWith` spine fold,
         * `reconstructRemainder` and both premise chain folds.
         *
         * They are deliberately ONE bucket rather than four: they all reach the same choke point
         * with a state their caller supplied, so a mint here means some caller failed to supply one,
         * and the useful signal is "any of them leaked" rather than which. An earlier split had a
         * `spineRebuild` bucket that was structurally unreachable and therefore always read zero,
         * which is worse than no bucket at all.
         */
        const val MINT_RAW_EDGE = 2
        const val MINT_BULK_MERGE = 3
        const val MINT_TEST = 4
        const val MINT_SITE_COUNT = 5

        val MINT_SITE_NAMES = arrayOf(
            "prepend", "deserialize", "rawEdge", "bulkMerge", "test"
        )
    }
}
