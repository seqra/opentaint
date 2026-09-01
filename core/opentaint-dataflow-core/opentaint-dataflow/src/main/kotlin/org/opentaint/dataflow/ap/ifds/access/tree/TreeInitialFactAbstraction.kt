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
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode as AccessTreeNode

class TreeInitialFactAbstraction(
    private val apManager: TreeApManager
): InitialFactAbstraction {
    private val initialFacts = MethodSameMarkInitialFact(apManager, hashMapOf())
    override fun addAbstractedInitialFact(
        factAp: FinalFactAp,
        typeChecker: FactTypeChecker
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        factAp as AccessTree

        // note: we can ignore fact exclusions here
        val facts = initialFacts.getOrPut(factAp.base)
        val addedFact = facts.addInitialFact(factAp.access) ?: return emptyList()

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

        val seed = facts.registerAnalyzedInitialFact(factAp.access, excludedAccessors) ?: return emptyList()

        val abstractFacts = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        addAbstractInitialFact(
            facts,
            factAp.base,
            seed.added,
            abstractFacts,
            typeChecker,
            seed.analyzedTrieRoot,
            seed.currentAp,
        )
        return abstractFacts
    }

    private fun addAbstractInitialFact(
        facts: MethodSameBaseInitialFact,
        concreteFactBase: AccessPathBase,
        initialConcreteFact: AccessTreeNode,
        abstractFacts: MutableList<Pair<InitialFactAp, FinalFactAp>>,
        typeChecker: FactTypeChecker,
        initialAnalyzedTrieRoot: AccessPathTrieNode = facts.analyzed,
        initialCurrentAp: ReversedApNode? = null,
    ) {
        var firstRound = true
        while (true) {
            var registeredNew = false
            abstractAccessPath(
                initialAnalyzedTrieRoot,
                initialConcreteFact,
                initialCurrentAp,
                typeChecker,
            ) { abstractAccess ->
                apManager.cancellation.checkpoint()

                val initialAbstractAccessNode = apManager.createNodeFromReversedAp(abstractAccess)
                val initialAbstractAp = apManager.internInitialFact(
                    concreteFactBase,
                    initialAbstractAccessNode,
                    Empty,
                )

                val apAccess = apManager.createAbstractNodeFromReversedAp(abstractAccess)
                val ap = apManager.internFinalFact(concreteFactBase, apAccess, Empty)

                val registered = facts.addAnalyzedInitialFact(initialAbstractAccessNode, exclusions = IntOpenHashSet())
                if (registered) registeredNew = true
                if (firstRound || registered) abstractFacts.add(initialAbstractAp to ap)
            }

            firstRound = false
            if (!registeredNew) break
        }
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
    private fun AccessorIdx.isUncoveredByAny(): Boolean =
        isAlwaysUnrollNext() || isStaticAccessor() || !apManager.isCoveredByAny(this)

    private fun AccessTreeNode.hasLiteralChild(accessor: AccessorIdx): Boolean =
        if (accessor == FINAL_ACCESSOR_IDX) isFinal else (accessors?.binarySearch(accessor) ?: -1) >= 0

    data class AbstractionState(
        val analyzedTrieRoot: AccessPathTrieNode,
        val added: AccessTreeNode,
        val currentAp: ReversedApNode?,
    )

    private inline fun abstractAccessPath(
        initialAnalyzedTrieRoot: AccessPathTrieNode,
        initialAdded: AccessTreeNode,
        initialCurrentAp: ReversedApNode?,
        typeChecker: FactTypeChecker,
        crossinline createAbstractAp: (ReversedApNode?) -> Unit
    ) {
        val unprocessed = mutableListOf<AbstractionState>()
        unprocessed.add(AbstractionState(initialAnalyzedTrieRoot, initialAdded, initialCurrentAp))

        while (unprocessed.isNotEmpty()) {
            val state = unprocessed.removeLast()

            val currentLevelExclusions = state.analyzedTrieRoot.exclusions()
            if (currentLevelExclusions == null) {
                createAbstractAp(state.currentAp)
                continue
            }

            val anyBranch = if (state.added.containsAnyAccessor()) {
                state.added.getChild(ANY_ACCESSOR_IDX)
            } else {
                null
            }
            if (anyBranch != null) {
                val anyTrie = state.analyzedTrieRoot.child(ANY_ACCESSOR_IDX)
                if (anyTrie != null) {
                    unprocessed += AbstractionState(
                        anyTrie,
                        anyBranch,
                        ReversedApNode(ANY_ACCESSOR_IDX, state.currentAp),
                    )
                }

                anyBranch.forEachAccessor { accessor, node ->
                    if (accessor == ANY_ACCESSOR_IDX || !accessor.isUncoveredByAny()) return@forEachAccessor
                    abstractAccessPath(
                        state.analyzedTrieRoot,
                        accessor,
                        node,
                        state.currentAp,
                        unprocessed,
                        createAbstractAp,
                    )
                }

                var accessorFilter: FactTypeChecker.FactApFilter? = null
                currentLevelExclusions.forEachInt { accessor ->
                    if (state.analyzedTrieRoot.child(accessor) != null) return@forEachInt
                    if (state.added.hasLiteralChild(accessor)) return@forEachInt
                    if (accessor.isUncoveredByAny()) return@forEachInt

                    val filter = accessorFilter
                        ?: state.currentAp.createFilter(typeChecker).also { accessorFilter = it }
                    when (filter.check(with(apManager) { accessor.accessor })) {
                        is FactTypeChecker.FilterResult.Accept,
                        is FactTypeChecker.FilterResult.FilterNext -> {
                        }
                        is FactTypeChecker.FilterResult.Reject -> return@forEachInt
                    }
                    createAbstractAp(ReversedApNode(accessor, state.currentAp))
                }
            }

            if (state.added.isFinal) {
                val node = apManager.create()
                abstractAccessPath(state.analyzedTrieRoot, FINAL_ACCESSOR_IDX, node, state.currentAp, unprocessed, createAbstractAp)
            }

            state.added.forEachAccessor { accessor, node ->
                if (accessor == ANY_ACCESSOR_IDX) return@forEachAccessor
                abstractAccessPath(state.analyzedTrieRoot, accessor, node, state.currentAp, unprocessed, createAbstractAp)
            }

            if (anyBranch != null) {
                state.analyzedTrieRoot.forEachChild { accessor, childTrie ->
                    if (accessor == ANY_ACCESSOR_IDX) return@forEachChild
                    if (state.added.hasLiteralChild(accessor)) return@forEachChild
                    if (accessor.isUncoveredByAny()) return@forEachChild

                    val child = state.added.getChild(accessor) ?: return@forEachChild
                    unprocessed += AbstractionState(
                        childTrie,
                        child,
                        ReversedApNode(accessor, state.currentAp),
                    )
                }
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

    private fun abstractNextAccessPath(
        addedNode: AccessTreeNode,
        currentAp: ReversedApNode,
        createAbstractAp: (ReversedApNode) -> Unit
    ) {
        if (addedNode.containsAnyAccessor()) {
            TODO("Any after unroll-next is not supported yet")
        }

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

        fun addInitialFact(ap: AccessTreeNode): AccessTreeNode? {
            val currentNode = added ?: manager.create()
            val (updatedAddedNode, addedInitial) = currentNode.mergeAddDelta(ap, foldToAny = false)

            if (addedInitial == null) return null

            this.added = internIfRequired(updatedAddedNode)

            intern()

            return addedInitial
        }

        private var operationsBeforeIntern = INTERN_RATE

        private fun internIfRequired(node: AccessTreeNode): AccessTreeNode {
            if (node.size < SIZE_TO_FORCE_INTERN) return node
            return manager.canonicalizeAccessTree(node)
        }

        private fun intern() {
            val current = added ?: return

            if (operationsBeforeIntern-- > 0) return
            if (current.size < INTERN_SIZE_REQUIREMENT) return

            operationsBeforeIntern = INTERN_RATE
            added = manager.canonicalizeAccessTree(current)
        }

        fun addAnalyzedInitialFact(ap: AccessPath.AccessNode?, exclusions: IntOpenHashSet): Boolean =
            AccessPathTrieNode.add(analyzed, ap, exclusions)

        fun registerAnalyzedInitialFact(
            ap: AccessPath.AccessNode?,
            exclusions: IntOpenHashSet,
        ): AbstractionSeed? {
            var trieNode = analyzed
            var addedNode: AccessTreeNode? = allAddedFacts()
            var access = ap
            var currentAp: ReversedApNode? = null

            while (access != null) {
                val childTrie = trieNode.child(access.accessor) ?: break
                addedNode = addedNode?.abstractionChild(access.accessor)
                currentAp = ReversedApNode(access.accessor, currentAp)
                trieNode = childTrie
                access = access.next
            }

            if (!addAnalyzedInitialFact(ap, exclusions)) return null
            val seedNode = addedNode ?: return null
            return AbstractionSeed(trieNode, seedNode, currentAp)
        }

        private fun AccessTreeNode.abstractionChild(accessor: AccessorIdx): AccessTreeNode? {
            if (accessor == FINAL_ACCESSOR_IDX) return manager.finalNode.takeIf { isFinal }

            val index = accessors?.binarySearch(accessor) ?: -1
            if (index >= 0) return accessorNodeAt(index)
            val uncovered = accessor.isAlwaysUnrollNext() ||
                accessor.isStaticAccessor() ||
                !manager.isCoveredByAny(accessor)
            if (uncovered || !containsAnyAccessor()) return null
            return getChild(accessor)
        }
    }

    data class AbstractionSeed(
        val analyzedTrieRoot: AccessPathTrieNode,
        val added: AccessTreeNode,
        val currentAp: ReversedApNode?,
    )

    class AccessPathTrieNode {
        private var children: Int2ObjectOpenHashMap<AccessPathTrieNode>? = null
        private var terminals: IntOpenHashSet? = null

        fun exclusions(): IntOpenHashSet? = terminals

        fun child(accessor: AccessorIdx): AccessPathTrieNode? =
            children?.get(accessor)

        fun forEachChild(body: (AccessorIdx, AccessPathTrieNode) -> Unit) {
            val iterator = children?.int2ObjectEntrySet()?.fastIterator() ?: return
            while (iterator.hasNext()) {
                val entry = iterator.next()
                body(entry.intKey, entry.value)
            }
        }

        private fun getTerminals(): IntOpenHashSet =
            terminals ?: IntOpenHashSet().also { terminals = it }

        private fun getChildren(): Int2ObjectOpenHashMap<AccessPathTrieNode> =
            children ?: Int2ObjectOpenHashMap<AccessPathTrieNode>().also { children = it }

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
