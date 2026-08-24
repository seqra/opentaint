package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.ExclusionSet.Empty
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAbstraction
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.ReversedApNode
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.createNodeFromReversedAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.foldRight
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.createAbstractNodeFromReversedAp
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isAlwaysUnrollNext
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode as AccessTreeNode

/**
 * The budget this used to carry itself now lives on [TreeApManager.anyUnroll], keyed by `[any]`
 * ORIGIN rather than by `(method entry point, access-path base)`.
 *
 * That is not a refactor for tidiness. A single-rule, single-entry-point witness had 7,347 distinct
 * `(entry point, base)` pairs, so a limit of 100 was an effective global allowance of ~735,000: the
 * cap was not weak because 100 is a large number, it was weak because it was multiplied by seven
 * thousand independent buckets. And it could only ever see the ONE channel that reaches this file --
 * capping it did not remove work, it diverted it to the spine rebuilds and the summary graft, which
 * measured a TWELVEFOLD increase in total materialisation at cap 0.
 */
class TreeInitialFactAbstraction(
    private val apManager: TreeApManager,
): InitialFactAbstraction {
    private val anyUnroll = apManager.anyUnroll
    private val initialFacts = MethodSameMarkInitialFact(apManager, hashMapOf())
    private val interner = AccessTreeSoftInterner(apManager)

    override fun addAbstractedInitialFact(
        factAp: FinalFactAp,
        typeChecker: FactTypeChecker
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        factAp as AccessTree

        // note: we can ignore fact exclusions here
        val facts = initialFacts.getOrPut(factAp.base)
        val addedFact = facts.addInitialFact(factAp.access, interner) ?: return emptyList()

        val abstractFacts = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        addAbstractInitialFact(facts, factAp.base, addedFact, abstractFacts, typeChecker)
        return abstractFacts
    }

    override fun registerNewInitialFact(
        factAp: InitialFactAp,
        typeChecker: FactTypeChecker
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        factAp as AccessPath

        val facts = initialFacts.getOrPut(factAp.base)

        val excludedAccessors = IntOpenHashSet()
        when (val ex = factAp.exclusions) {
            is ExclusionSet.Concrete -> ex.set.forEach {
                with(apManager) { excludedAccessors.add(it.idx) }
            }
            Empty -> {
                // do nothing
            }
            ExclusionSet.Universe -> error("Unexpected universe exclusion")
        }

        if (!facts.addAnalyzedInitialFact(factAp.access, excludedAccessors)) return emptyList()

        val abstractFacts = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        addAbstractInitialFact(facts, factAp.base, facts.allAddedFacts(), abstractFacts, typeChecker)
        return abstractFacts
    }

    private fun addAbstractInitialFact(
        facts: MethodSameBaseInitialFact,
        concreteFactBase: AccessPathBase,
        initialConcreteFact: AccessTreeNode,
        abstractFacts: MutableList<Pair<InitialFactAp, FinalFactAp>>,
        typeChecker: FactTypeChecker
    ) {
        var concreteFactAccess = initialConcreteFact
        var enumerateAnyFrontier = true
        while (true) {
            val unrollRequests = mutableListOf<AnyAccessorUnrollRequest>()
            abstractAccessPath(facts.analyzed, concreteFactAccess, unrollRequests, enumerateAnyFrontier) { abstractAccess, governingAnyId ->
                apManager.cancellation.checkpoint()

                val initialAbstractAccessNode = apManager.createNodeFromReversedAp(abstractAccess)
                val initialAbstractAp = AccessPath(apManager, concreteFactBase, initialAbstractAccessNode, Empty)

                // The emitted fact INHERITS the walk's governing state rather than minting one.
                // Minting per emission would restore a per-premise budget -- finer than the
                // per-`(entry point, base)` counter this replaces, and wrong the same way. The
                // predecessor exists and the walk is holding it: the `[any]` in the emitted chain is
                // not invented, it is the `[any]` edge the walk crossed.
                val apAccess = apManager.createAbstractNodeFromReversedAp(abstractAccess, governingAnyId)
                val ap = AccessTree(apManager, concreteFactBase, apAccess, Empty)

                facts.addAnalyzedInitialFact(initialAbstractAccessNode, exclusions = IntOpenHashSet())
                abstractFacts.add(initialAbstractAp to ap)
            }

            if (!enumerateAnyFrontier) break

            val unrolled = unrollAnyAccessors(facts, unrollRequests, typeChecker)

            if (unrolled.budgetSpent) {
                // A pot ran out during this round -- either an accessor was refused outright, or the
                // last one it granted took the pot to its limit. Two things then have to happen at
                // once, and neither survives simply breaking out of the loop.
                //
                // The refused accessors have already been consumed from `AccessPathTrieNode`'s
                // one-shot memo, so nothing would answer them any more. And the round after this one
                // would walk only the newly unrolled DELTA, whose root is a concrete accessor -- the
                // `[any]` that needs summarising sits at the root of the base's whole fact set, not
                // of the delta. So: walk the whole set once more, coarsely, which emits the `[any]`
                // premise for every frontier that carries demand, and stop.
                enumerateAnyFrontier = false
                concreteFactAccess = facts.allAddedFacts()
                continue
            }

            concreteFactAccess = unrolled.node ?: break
        }
    }

    private class UnrollResult(val node: AccessTreeNode?, val budgetSpent: Boolean)

    private fun unrollAnyAccessors(
        facts: MethodSameBaseInitialFact,
        unrollRequests: List<AnyAccessorUnrollRequest>,
        typeChecker: FactTypeChecker
    ): UnrollResult {
        if (unrollRequests.isEmpty()) return UnrollResult(null, budgetSpent = false)

        val unrollStrategy = apManager.anyAccessorUnrollStrategy

        var budgetSpent = false
        val newFacts = mutableListOf<AccessTreeNode>()
        for (unrollRequest in unrollRequests) {
            apManager.cancellation.checkpoint()

            // The state of the `[any]` edge this request is unrolling. The request captures the node
            // that CARRIES the edge, not the `[any]` subtree, so this is the right one.
            val parentAnyState = unrollRequest.node.anyId

            unrollRequest.accessors.forEachInt { accessor ->
                val accessorInstance = with(apManager) { accessor.accessor }
                if (!unrollStrategy.unrollAccessor(accessorInstance)) return@forEachInt

                // The unroll IS an R4 read: `R.[any]` denotes `R`, `R.x`, `R.x.y`, ... while
                // `R.f.[any]` denotes `R.f`, `R.f.x`, ... -- a strict subset with exactly one step
                // spent. It is tempting to read the surviving `[any]` edge as "duplicated, not
                // consumed" and keep the parent's state; that is a refill. Unroll `f` then `g` and
                // read `p` under each: keeping the parent, both record `child(p)`, the second is
                // free, and the automaton stays one level deep however wide the fan-out. Advancing,
                // they record `child(f).child(p)` and `child(g).child(p)` -- two paths, two
                // accessors, which is the population the bound is about.
                val childAnyState = anyUnroll.readChild(parentAnyState, accessor)
                if (anyUnroll.enabled && parentAnyState != null && childAnyState == null) {
                    budgetSpent = true
                    return@forEachInt
                }

                val accessorFilter = unrollRequest.currentAp.createFilter(typeChecker)
                val accessorStatus = accessorFilter.check(accessorInstance)
                when (accessorStatus) {
                    is FactTypeChecker.FilterResult.Accept,
                    is FactTypeChecker.FilterResult.FilterNext -> {
                        // accept
                    }

                    is FactTypeChecker.FilterResult.Reject -> return@forEachInt
                }

                val prefix = ReversedApNode(accessor, unrollRequest.currentAp)

                val nodeFilter = prefix.createFilter(typeChecker)
                val filteredNode = unrollRequest.node.filterAccessNode(nodeFilter) ?: return@forEachInt

                newFacts += filteredNode.withAnyState(childAnyState)
                    .addReversedApParents(prefix, unrollRequest.governingAnyId)
                    ?: return@forEachInt
            }

            // Not only an outright refusal: an unroll that took the pot exactly to its limit leaves
            // nothing for the next round either, and the coarse premise still has to be emitted.
            if (anyUnroll.budgetExhausted(parentAnyState)) budgetSpent = true
        }

        val mergedNewFacts = newFacts.reduceOrNull { acc, f -> acc.mergeAdd(f, foldToAny = false) }
            ?: return UnrollResult(null, budgetSpent)

        return UnrollResult(facts.addInitialFact(mergedNewFacts, interner), budgetSpent)
    }

    private fun ReversedApNode?.createFilter(typeChecker: FactTypeChecker): FactTypeChecker.FactApFilter {
        val accessors = mutableListOf<Accessor>()
        foldRight(Unit) { accessor, _ ->
            with(apManager) {
                accessors.add(accessor.accessor)
            }
        }
        return typeChecker.accessPathFilter(accessors.asReversed())
    }

    private fun AccessTreeNode.addReversedApParents(
        ap: ReversedApNode,
        governingAnyId: AnyUnrollState?,
    ): AccessTreeNode? =
        ap.foldRight(this) { accessor, node ->
            // `currentAp` can carry an `[any]` link -- the walk pushes one at every `[any]` descent
            // -- and re-creating that edge with no state would derive R1/R2 from the subtree. That
            // is a full fresh pot whenever the type filter has already stripped the subtree's own
            // `[any]`, which is exactly the refill the rest of this file is threaded to avoid.
            node.addParentIfPossible(accessor, governingAnyId) ?: return null
        }

    data class AbstractionState(
        val analyzedTrieRoot: AccessPathTrieNode,
        val added: AccessTreeNode,
        val currentAp: ReversedApNode?,
        /**
         * The `[any]` manager state the walk is under, or null above every `[any]`.
         *
         * One reference per walk state and no set, because the branch invariant guarantees a walk
         * down one path meets exactly one manager. It travels on the FACT side only -- the emitted
         * `AccessPath` gets nothing, and that matters more than it looks: premise identity keys the
         * whole demand system, and two premises differing only by an annotation would be two
         * demands.
         */
        val governingAnyId: AnyUnrollState?,
    )

    data class AnyAccessorUnrollRequest(
        val currentAp: ReversedApNode?,
        val node: AccessTreeNode,
        val accessors: IntOpenHashSet,
        /** The state governing any `[any]` link already in [currentAp]; see [addReversedApParents]. */
        val governingAnyId: AnyUnrollState?,
    )

    private inline fun abstractAccessPath(
        initialAnalyzedTrieRoot: AccessPathTrieNode,
        initialAdded: AccessTreeNode,
        unrollRequests: MutableList<AnyAccessorUnrollRequest>,
        enumerateAnyFrontier: Boolean,
        crossinline createAbstractAp: (ReversedApNode?, AnyUnrollState?) -> Unit
    ) {
        val unprocessed = mutableListOf<AbstractionState>()
        unprocessed.add(AbstractionState(initialAnalyzedTrieRoot, initialAdded, currentAp = null, governingAnyId = null))

        while (unprocessed.isNotEmpty()) {
            val state = unprocessed.removeLast()

            val currentLevelExclusions = state.analyzedTrieRoot.exclusions()
            if (currentLevelExclusions == null) {
                createAbstractAp(state.currentAp, state.governingAnyId)
                continue
            }

            if (state.added.containsAnyAccessor()) {
                // The budget is consulted BEFORE the memo, deliberately.
                // `AccessPathTrieNode.unrollAccessors` commits as it reads and has no un-take, so
                // collecting a request we will not honour burns demand that a later, better-funded
                // state could have served.
                val enumerateHere = enumerateAnyFrontier && !anyUnroll.budgetExhausted(state.added.anyId)

                if (enumerateHere) {
                    val unrollAccessors = state.analyzedTrieRoot.unrollAccessors(currentLevelExclusions)
                    if (unrollAccessors.isNotEmpty()) {
                        unrollRequests += AnyAccessorUnrollRequest(
                            state.currentAp, state.added, unrollAccessors, state.governingAnyId,
                        )
                    }
                }

                val anyBranch = state.added.getChild(ANY_ACCESSOR_IDX) ?: error("impossible")

                // (1) The `[any]` taken ZERO times. `[any]` is zero-or-more (§3.5), so the fact also
                // denotes every path that skips it, and `AccessTree.getChild` hoists a child of the
                // `[any]` node up to this level -- which is exactly why an `[any]`-FREE premise
                // matches an `[any]`-carrying fact. Keeping this descent is what keeps answering the
                // demands registered at THIS trie level: a sink precondition `<this>.![m].$` sits at
                // `root -> mark`, and a fact `this.[any].![m].$` has no mark child of its own, so the
                // mark is reachable in the walk only through here. Dropping it is the shape that lost
                // conductor's `ssrf` and `path-traversal` in the earlier prototypes (§3.2).
                unprocessed += AbstractionState(state.analyzedTrieRoot, anyBranch, state.currentAp, state.governingAnyId)

                // (2) The `[any]` as an ordinary accessor (§3.1): descend the trie THROUGH it, so the
                // prefix and the trie node stay in step, and premises emitted below it name the
                // `[any]`. The two descents are not redundant -- they walk different trie nodes and
                // emit disjoint premise families, `[any]`-free above and `[any]`-carrying here.
                //
                // The rule is the per-accessor helper's, with two substitutions. An analysed trie
                // child means the premise was already handed out, so walk on -- unconditionally,
                // because a premise below an `[any]` (a mark, §3.2) is demanded exactly as any other
                // deeper premise is. Otherwise emit it, but only where the level carries demand AND
                // this base has stopped enumerating. The helper tests `exclusions.contains(a)`,
                // which can never hold for `[any]` (exclusion sets are only ever populated from
                // concrete accessors), so the demand test here is that the level has ANY demand at
                // all -- every excluded accessor is one this `[any]` covers.
                //
                // The `!enumerateAnyFrontier` half is design §7 R5, and it is not an optimisation.
                // The `[any]` premise summarises the whole frontier in one coarse edge: its entry
                // fact `R.[any].*` cannot express a node deletion inside the `[any]`, so a cleaner
                // that bites on a concrete path stops biting under it. Emitting it ALONGSIDE the
                // enumeration therefore only adds false positives -- measured:
                // `TreeCleanerFieldSensitivityAnalysisTest.concrete two-level clean over an abstract
                // source` resurrects the cleaned field. Past the cap the coarse edge is the only
                // thing answering the demand, and the trade is then the point.
                val anyAp = ReversedApNode(ANY_ACCESSOR_IDX, state.currentAp)
                val anyTrieRoot = state.analyzedTrieRoot.child(ANY_ACCESSOR_IDX)
                // The premise emitted below this point NAMES the `[any]`, so it is governed by the
                // state of the edge just crossed.
                val anyGoverning = state.added.anyId ?: state.governingAnyId
                when {
                    anyTrieRoot != null -> unprocessed += AbstractionState(anyTrieRoot, anyBranch, anyAp, anyGoverning)
                    !enumerateHere && currentLevelExclusions.isNotEmpty() -> createAbstractAp(anyAp, anyGoverning)
                }
            }

            // No `state.added.isFinal` branch here (§7 R7). It used to call the per-accessor helper
            // with `FINAL_ACCESSOR_IDX` and an EMPTY node, and every path through the helper then
            // emitted nothing: `[final]` is always-unroll-next, so it either descended into
            // `abstractNextAccessPath` with a node that has no children and is not final, or returned
            // on the exclusion test. It was dead in all four cases, so deleting it cannot change a
            // result. The premise it looked like it was reaching for, `R.$`, is not needed either:
            // the `.*` completion of the premise at `R` already covers `$`, and the only shape that
            // would require naming it is an exclusion set containing `FinalAccessor`, which no flow
            // function produces -- exclusions come from field/element assignment refinement
            // (`propagateFactWithAccessorExclude`) and from `TypeInfoGroupAccessor`
            // (`CallTypeInfoUtil`).
            state.added.forEachAccessor { accessor, node ->
                // `[any]` is owned by the block above, which sees the same child through `getChild`.
                // Routing it through the helper as well would be a plain duplicate: the helper pushes
                // the identical state when `analyzedTrieRoot.child(ANY)` exists, and contributes
                // nothing when it does not, since `exclusions.contains(ANY)` is never true.
                if (accessor == ANY_ACCESSOR_IDX) return@forEachAccessor

                abstractAccessPath(
                    state.analyzedTrieRoot, accessor, node, state.currentAp, state.governingAnyId,
                    unprocessed, createAbstractAp,
                )
            }
        }
    }

    private inline fun abstractAccessPath(
        analyzedTrieRoot: AccessPathTrieNode,
        accessor: AccessorIdx,
        addedNode: AccessTreeNode,
        currentAp: ReversedApNode?,
        governingAnyId: AnyUnrollState?,
        unprocessed: MutableList<AbstractionState>,
        crossinline createAbstractAp: (ReversedApNode?, AnyUnrollState?) -> Unit
    ) {
        val node = analyzedTrieRoot.child(accessor)
        if (node != null) {
            val apWithAccessor = ReversedApNode(accessor, currentAp)
            if (accessor.isAlwaysUnrollNext()) {
                abstractNextAccessPath(addedNode, apWithAccessor, governingAnyId) { ap, governing ->
                    createAbstractAp(ap, governing)
                }
            } else {
                unprocessed += AbstractionState(node, addedNode, apWithAccessor, governingAnyId)
            }
            return
        }

        val exclusions = analyzedTrieRoot.exclusions()

        // We have no excludes -> continue with the most abstract fact
        if (exclusions == null) {
            createAbstractAp(currentAp, governingAnyId)
            return
        }

        // Concrete: a.b.* E
        // Added: a.* S
        if (!exclusions.contains(accessor)) {
            // We have no conflict with added facts
            return
        }

        // We have initial fact that exclude {b} and we have no a.b fact yet
        if (!accessor.isAlwaysUnrollNext()) {
            // Return a.b.* {}
            createAbstractAp(ReversedApNode(accessor, currentAp), governingAnyId)
            return
        }

        val apWithAccessor = ReversedApNode(accessor, currentAp)
        abstractNextAccessPath(addedNode, apWithAccessor, governingAnyId) { ap, governing ->
            createAbstractAp(ap, governing)
        }
    }

    /**
     * The continuation below an always-unroll-next accessor (a taint mark, `[final]`, `[value]`, a
     * type-info accessor). There is no trie and no demand test here: a premise may not stop at such
     * an accessor, so every branch below it is emitted, and the recursion runs until it reaches one
     * that a premise may stop at.
     *
     * `[any]` needs no case of its own (§7 R6, which the `TODO` this replaces stood for). It is not
     * always-unroll-next, so the loop below emits `currentAp.[any]` and stops -- an ordinary
     * accessor, the same shape [abstractAccessPath] emits, and its `.*` completion covers the whole
     * subtree the `[any]` carried.
     *
     * The reachable shapes are `[any]` under `[value]` or under a type-info accessor. `[any]` under a
     * taint mark is unconstructible -- `AccessTree.AccessNode.create` bans a mark above a structured
     * node -- which is also what keeps the emitted chain legal: `createAbstractNodeFromReversedAp`
     * would otherwise have to build a mark above an `[any]` node and would fail that same check.
     */
    private fun abstractNextAccessPath(
        addedNode: AccessTreeNode,
        currentAp: ReversedApNode,
        governingAnyId: AnyUnrollState?,
        createAbstractAp: (ReversedApNode, AnyUnrollState?) -> Unit
    ) {
        if (addedNode.isFinal) {
            createAbstractAp(ReversedApNode(FINAL_ACCESSOR_IDX, currentAp), governingAnyId)
        }

        addedNode.forEachAccessor { accessor, node ->
            val nextAp = ReversedApNode(accessor, currentAp)
            val nextGoverning =
                if (accessor == ANY_ACCESSOR_IDX) addedNode.anyId ?: governingAnyId else governingAnyId
            if (!accessor.isAlwaysUnrollNext()) {
                createAbstractAp(nextAp, nextGoverning)
            } else {
                abstractNextAccessPath(node, nextAp, nextGoverning, createAbstractAp)
            }
        }
    }

    private class MethodSameMarkInitialFact(
        val manager: TreeApManager,
        val facts: MutableMap<AccessPathBase, MethodSameBaseInitialFact>
    ) {
        fun getOrPut(base: AccessPathBase): MethodSameBaseInitialFact = facts.getOrPut(base) {
            MethodSameBaseInitialFact(manager, added = null, AccessPathTrieNode.empty())
        }
    }

    private class MethodSameBaseInitialFact(
        val manager: TreeApManager,
        private var added: AccessTreeNode?,
        val analyzed: AccessPathTrieNode
    ) {
        fun allAddedFacts(): AccessTreeNode = added ?: manager.create()

        fun addInitialFact(ap: AccessTreeNode, interner: AccessTreeSoftInterner): AccessTreeNode? {
            val currentNode = added ?: manager.create()
            val (updatedAddedNode, addedInitial) = currentNode.mergeAddDelta(ap, foldToAny = false)

            if (addedInitial == null) return null

            this.added = internIfRequired(interner, updatedAddedNode)

            intern(interner)

            return addedInitial
        }

        private var operationsBeforeIntern = INTERN_RATE

        private fun internIfRequired(interner: AccessTreeSoftInterner, node: AccessTreeNode): AccessTreeNode {
            if (node.size < SIZE_TO_FORCE_INTERN) return node
            return interner.intern(node)
        }

        private fun intern(interner: AccessTreeSoftInterner) {
            val current = added ?: return

            if (operationsBeforeIntern-- > 0) return
            if (current.size < INTERN_SIZE_REQUIREMENT) return

            operationsBeforeIntern = INTERN_RATE
            added = interner.intern(current)
        }

        fun addAnalyzedInitialFact(ap: AccessPath.AccessNode?, exclusions: IntOpenHashSet): Boolean =
            AccessPathTrieNode.add(analyzed, ap, exclusions)
    }

    class AccessPathTrieNode {
        private var children: Int2ObjectOpenHashMap<AccessPathTrieNode>? = null
        private var terminals: IntOpenHashSet? = null
        private var unrolled: IntOpenHashSet? = null

        fun exclusions(): IntOpenHashSet? = terminals

        fun child(accessor: AccessorIdx): AccessPathTrieNode? =
            children?.get(accessor)

        private fun getTerminals(): IntOpenHashSet =
            terminals ?: IntOpenHashSet().also { terminals = it }

        private fun getChildren(): Int2ObjectOpenHashMap<AccessPathTrieNode> =
            children ?: Int2ObjectOpenHashMap<AccessPathTrieNode>().also { children = it }

        fun unrollAccessors(accessors: IntOpenHashSet): IntOpenHashSet {
            val current = unrolled ?: IntOpenHashSet().also { unrolled = it }
            val result = IntOpenHashSet()
            accessors.forEachInt {
                if (current.add(it)) result.add(it)
            }
            return result
        }

        companion object {
            fun empty() = AccessPathTrieNode()

            fun add(
                initialRoot: AccessPathTrieNode,
                initialAccess: AccessPath.AccessNode?,
                exclusions: IntOpenHashSet,
            ): Boolean {
                var trieNode = initialRoot
                var access = initialAccess

                while (true) {
                    if (access == null) {
                        var modified = trieNode.terminals == null
                        modified = modified or trieNode.getTerminals().addAll(exclusions)
                        return modified
                    }

                    val key = access.accessor
                    trieNode = trieNode.getChildren().getOrPut(key) { empty() }
                    access = access.next
                }
            }
        }
    }

    companion object {
        private const val INTERN_RATE = 100
        private const val INTERN_SIZE_REQUIREMENT = 1_000
        private const val SIZE_TO_FORCE_INTERN = 100_000
    }
}
