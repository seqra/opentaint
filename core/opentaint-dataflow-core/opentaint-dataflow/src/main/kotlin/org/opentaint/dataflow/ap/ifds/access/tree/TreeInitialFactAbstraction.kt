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

class TreeInitialFactAbstraction(
    private val apManager: TreeApManager,
    /**
     * How many concrete facts a single `(method entry point, access-path base)` may materialise out
     * of an `[any]` accessor before this abstraction stops unrolling that base. See
     * [ANY_UNROLL_LIMIT]; negative means no cap. A parameter rather than a direct read of the
     * companion value so that a test can pin a limit without touching global state.
     */
    private val anyUnrollLimit: Int = ANY_UNROLL_LIMIT,
): InitialFactAbstraction {
    private val initialFacts = MethodSameMarkInitialFact(apManager, anyUnrollLimit, hashMapOf())
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
        while (true) {
            // Once the base is cut (§3.3) the walk must not even COLLECT unroll requests:
            // `AccessPathTrieNode.unrollAccessors` commits as it reads, so collecting a request we
            // will not honour would burn the memo for nothing. The same flag is what switches the
            // walk from enumerating a frontier to summarising it with an `[any]` premise.
            val enumerateAnyFrontier = facts.anyUnrollAllowed
            val unrollRequests = mutableListOf<AnyAccessorUnrollRequest>()
            abstractAccessPath(facts.analyzed, concreteFactAccess, unrollRequests, enumerateAnyFrontier) { abstractAccess ->
                apManager.cancellation.checkpoint()

                val initialAbstractAccessNode = apManager.createNodeFromReversedAp(abstractAccess)
                val initialAbstractAp = AccessPath(apManager, concreteFactBase, initialAbstractAccessNode, Empty)

                val apAccess = apManager.createAbstractNodeFromReversedAp(abstractAccess)
                val ap = AccessTree(apManager, concreteFactBase, apAccess, Empty)

                facts.addAnalyzedInitialFact(initialAbstractAccessNode, exclusions = IntOpenHashSet())
                abstractFacts.add(initialAbstractAp to ap)
            }

            if (!enumerateAnyFrontier) break

            val unrolled = facts.unrollAnyAccessors(unrollRequests, typeChecker)

            if (!facts.anyUnrollAllowed) {
                // The cap tripped inside this very round. The frontiers this round walked were
                // walked while still enumerating, and the accessors it refused to unroll after the
                // limit was reached have already been consumed from the one-shot `unrolled` memo,
                // so nothing would answer them. Walk the base's whole fact set once more, coarsely:
                // that round emits the `[any]` premise for every frontier that carries demand.
                concreteFactAccess = facts.allAddedFacts()
                continue
            }

            concreteFactAccess = unrolled ?: break
        }
    }

    private fun MethodSameBaseInitialFact.unrollAnyAccessors(
        unrollRequests: List<AnyAccessorUnrollRequest>,
        typeChecker: FactTypeChecker
    ): AccessTreeNode? {
        if (unrollRequests.isEmpty()) return null

        val unrollStrategy = apManager.anyAccessorUnrollStrategy

        val newFacts = mutableListOf<AccessTreeNode>()
        for (unrollRequest in unrollRequests) {
            apManager.cancellation.checkpoint()

            unrollRequest.accessors.forEachInt { accessor ->
                // The cap is checked per materialised fact, not per request: a request carries a
                // whole exclusion set and the limit may be reached in the middle of one.
                if (!anyUnrollAllowed) return@forEachInt

                val accessorInstance = with(apManager) { accessor.accessor }
                if (!unrollStrategy.unrollAccessor(accessorInstance)) return@forEachInt

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

                newFacts += filteredNode.addReversedApParents(prefix)
                    ?: return@forEachInt

                accountUnrolledFact()
            }
        }

        val mergedNewFacts = newFacts.reduceOrNull { acc, f -> acc.mergeAdd(f, foldToAny = false) }
            ?: return null

        return addInitialFact(mergedNewFacts, interner)
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

    private fun AccessTreeNode.addReversedApParents(ap: ReversedApNode): AccessTreeNode? =
        ap.foldRight(this) { accessor, node ->
            node.addParentIfPossible(accessor) ?: return null
        }

    data class AbstractionState(
        val analyzedTrieRoot: AccessPathTrieNode,
        val added: AccessTreeNode,
        val currentAp: ReversedApNode?,
    )

    data class AnyAccessorUnrollRequest(
        val currentAp: ReversedApNode?,
        val node: AccessTreeNode,
        val accessors: IntOpenHashSet,
    )

    private inline fun abstractAccessPath(
        initialAnalyzedTrieRoot: AccessPathTrieNode,
        initialAdded: AccessTreeNode,
        unrollRequests: MutableList<AnyAccessorUnrollRequest>,
        enumerateAnyFrontier: Boolean,
        crossinline createAbstractAp: (ReversedApNode?) -> Unit
    ) {
        val unprocessed = mutableListOf<AbstractionState>()
        unprocessed.add(AbstractionState(initialAnalyzedTrieRoot, initialAdded, currentAp = null))

        while (unprocessed.isNotEmpty()) {
            val state = unprocessed.removeLast()

            val currentLevelExclusions = state.analyzedTrieRoot.exclusions()
            if (currentLevelExclusions == null) {
                createAbstractAp(state.currentAp)
                continue
            }

            if (state.added.containsAnyAccessor()) {
                if (enumerateAnyFrontier) {
                    val unrollAccessors = state.analyzedTrieRoot.unrollAccessors(currentLevelExclusions)
                    if (unrollAccessors.isNotEmpty()) {
                        unrollRequests += AnyAccessorUnrollRequest(state.currentAp, state.added, unrollAccessors)
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
                unprocessed += AbstractionState(state.analyzedTrieRoot, anyBranch, state.currentAp)

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
                when {
                    anyTrieRoot != null -> unprocessed += AbstractionState(anyTrieRoot, anyBranch, anyAp)
                    !enumerateAnyFrontier && currentLevelExclusions.isNotEmpty() -> createAbstractAp(anyAp)
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

                abstractAccessPath(state.analyzedTrieRoot, accessor, node, state.currentAp, unprocessed, createAbstractAp)
            }
        }
    }

    private inline fun abstractAccessPath(
        analyzedTrieRoot: AccessPathTrieNode,
        accessor: AccessorIdx,
        addedNode: AccessTreeNode,
        currentAp: ReversedApNode?,
        unprocessed: MutableList<AbstractionState>,
        crossinline createAbstractAp: (ReversedApNode?) -> Unit
    ) {
        val node = analyzedTrieRoot.child(accessor)
        if (node != null) {
            val apWithAccessor = ReversedApNode(accessor, currentAp)
            if (accessor.isAlwaysUnrollNext()) {
                abstractNextAccessPath(addedNode, apWithAccessor) {
                    createAbstractAp(it)
                }
            } else {
                unprocessed += AbstractionState(node, addedNode, apWithAccessor)
            }
            return
        }

        val exclusions = analyzedTrieRoot.exclusions()

        // We have no excludes -> continue with the most abstract fact
        if (exclusions == null) {
            createAbstractAp(currentAp)
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
            createAbstractAp(ReversedApNode(accessor, currentAp))
            return
        }

        val apWithAccessor = ReversedApNode(accessor, currentAp)
        abstractNextAccessPath(addedNode, apWithAccessor) {
            createAbstractAp(it)
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
        createAbstractAp: (ReversedApNode) -> Unit
    ) {
        if (addedNode.isFinal) {
            createAbstractAp(ReversedApNode(FINAL_ACCESSOR_IDX, currentAp))
        }

        addedNode.forEachAccessor { accessor, node ->
            val nextAp = ReversedApNode(accessor, currentAp)
            if (!accessor.isAlwaysUnrollNext()) {
                createAbstractAp(nextAp)
            } else {
                abstractNextAccessPath(node, nextAp, createAbstractAp)
            }
        }
    }

    private class MethodSameMarkInitialFact(
        val manager: TreeApManager,
        val anyUnrollLimit: Int,
        val facts: MutableMap<AccessPathBase, MethodSameBaseInitialFact>
    ) {
        fun getOrPut(base: AccessPathBase): MethodSameBaseInitialFact = facts.getOrPut(base) {
            MethodSameBaseInitialFact(manager, anyUnrollLimit, added = null, AccessPathTrieNode.empty())
        }
    }

    private class MethodSameBaseInitialFact(
        val manager: TreeApManager,
        private val anyUnrollLimit: Int,
        private var added: AccessTreeNode?,
        val analyzed: AccessPathTrieNode
    ) {
        /**
         * How many concrete facts this base has materialised out of an `[any]` accessor.
         *
         * The counter never decreases, so [anyUnrollAllowed] flips false once and stays false: the
         * cut is sticky per base, which is what bounds the premise set a single base can contribute.
         * The count is per `(method entry point, access-path base)` because there is one
         * [TreeInitialFactAbstraction] per `NormalMethodAnalyzer` and one of these per base.
         */
        private var unrolledFactCount = 0

        val anyUnrollAllowed: Boolean
            get() = anyUnrollLimit < 0 || unrolledFactCount < anyUnrollLimit

        fun accountUnrolledFact() {
            unrolledFactCount++
        }

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

        private const val ANY_UNROLL_LIMIT_PROPERTY = "opentaint.anyUnrollLimit"

        /**
         * `-Dopentaint.anyUnrollLimit=<n>`: the cap of §3.3, off by default (§8.3).
         *
         * `n < 0` -- and that is the default -- means no cap, i.e. `[any]` unrolling behaves exactly
         * as it did before the cap existed. A non-negative `n` lets each
         * `(method entry point, access-path base)` materialise at most `n` concrete facts out of an
         * `[any]`, after which that base stops unrolling and relies on the `[any]` premise the walk
         * emits instead. Turning it on trades precision for enumeration size and is a decision to be
         * made from measurements on a converging workload, not a default.
         *
         * Read once, at class initialisation: the value is consulted per unrolled fact and a
         * `System.getProperty` there would show up in a profile.
         */
        private val ANY_UNROLL_LIMIT: Int = 100
//            System.getProperty(ANY_UNROLL_LIMIT_PROPERTY)?.trim()?.toIntOrNull() ?: -1
    }
}
