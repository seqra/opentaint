package org.opentaint.dataflow.ap.ifds.analysis.alias

import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntIntImmutablePair
import it.unimi.dsi.fastutil.ints.IntIntMutablePair
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.opentaint.dataflow.ap.ifds.analysis.alias.IntDisjointSets.RankStrategy
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.dataflow.util.mapIntTo

interface ImmutableState {
    fun mutableCopy(): State
    fun unsafeState(): State
}

class State private constructor(
    val manager: AAInfoManager,
    val aliasGroups: IntDisjointSets,
) : ImmutableState {

    override fun hashCode(): Int = error("Unsupported operation")

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is State) return false

        /**
         * We don't need to align heap instances here.
         * Since set repr selection is deterministic due to strategy,
         * if sets are equal their repr are also equal.
         * So, heap instances must be equal.
         * */
        return aliasGroups == other.aliasGroups
    }

    fun isEmpty(): Boolean = aliasGroups.isEmpty()

    fun asImmutable(): ImmutableState = this

    override fun unsafeState(): State = this
    override fun mutableCopy(): State = State(manager, aliasGroups.mutableCopy())

    fun removeUnsafe(infos: IntOpenHashSet): State {
        if (infos.isEmpty()) return this

        val normalizedInfos = fixHeapElementInstance(infos)
        val result = aliasGroups.mutableCopy()

        val removedInstances = IntOpenHashSet()
        result.prepareRemoveAll(normalizedInfos, removedInstances)

        val removeAfterHeapFix = IntOpenHashSet()
        restoreHeapInvariant(manager, result, removeAfterHeapFix)

        // since we use prepare-remove, old replaced roots are still in the DSU
        removeAfterHeapFix.addAll(normalizedInfos)
        result.removeAll(removeAfterHeapFix)

        if (removedInstances.isEmpty()) {
            return State(manager, result)
        }

        val removedHeap = IntOpenHashSet()
        result.allElements().forEachInt {
            if (!manager.isHeapAlias(it)) return@forEachInt

            val heapElement = manager.getHeapRefUnchecked(it)
            if (removedInstances.contains(heapElement.instance)) {
                removedHeap.add(it)
            }
        }

        return State(manager, result).removeUnsafe(removedHeap)
    }

    fun aliasGroupId(info: Int): Int = aliasGroups.find(info)
    fun aliasGroupRepr(groupId: Int): Int = aliasGroups.find(groupId)

    fun mergeAliasSets(aliasSets: IntOpenHashSet): State {
        if (aliasSets.size < 2) return this

        val firstRepr = aliasSets.intIterator().nextInt()
        val relations = mutableListOf<IntIntMutablePair>()
        aliasSets.forEachInt {
            if (it == firstRepr) return@forEachInt
            relations += IntIntMutablePair(firstRepr, it)
        }

        val result = aliasGroups.mutableCopy()
        mergeUnionRelations(relations, result, manager)

        return State(manager, result)
    }

    fun forEachAliasInSet(info: Int, body: (Int) -> Unit) = forEachAliasInSetWithBreak(info, body)

    fun forEachAliasInSetWithBreak(info: Int, body: (Int) -> Unit?) {
        aliasGroups.forEachElementInSet(info, body)
    }

    fun allAliasSets(): Collection<IntOpenHashSet> = aliasGroups.allSets()

    fun allSetElements(): IntOpenHashSet = aliasGroups.allElements()

    override fun toString(): String = buildString {
        for (aliasSet in allAliasSets()) {
            appendLine("{")
            aliasSet.forEachInt {
                appendLine("\t($it) -> ${manager.getElementUncheck(it)}")
            }
            appendLine("}")
        }
    }

    private fun fixHeapElementInstance(elements: IntOpenHashSet) =
        elements.mapIntTo(IntOpenHashSet(elements.size)) {
            ensureHeapElementCorrect(it, aliasGroups, manager)
        }

    fun translate(newManager: AAInfoManager, newStrategy: RankStrategy): State {
        val translationCache = Int2IntOpenHashMap().apply { defaultReturnValue(NO_VALUE) }
        val translatedAliasGroups = aliasGroups.translate(newStrategy) {
            translateElement(it, translationCache, newManager)
        }
        return State(newManager, translatedAliasGroups)
    }

    private fun translateElement(element: Int, cache: Int2IntOpenHashMap, newManager: AAInfoManager): Int {
        val current = cache.putIfAbsent(element, TRANSLATION_STARTED)
        if (current != NO_VALUE) {
            if (current == TRANSLATION_STARTED) {
                TODO("AA: recursive element translation")
            }
            return current
        }

        var currentInfo = manager.getElementUncheck(element)
        if (currentInfo is HeapAlias) {
            val translatedInstance = translateElement(currentInfo.instance, cache, newManager)
            currentInfo = manager.replaceHeapInstance(currentInfo, translatedInstance)
        }
        val result =  newManager.getOrAdd(currentInfo)

        cache.put(element, result)
        return result
    }

    companion object {
        private const val TRANSLATION_STARTED = Int.MAX_VALUE
        private const val NO_VALUE = Int.MIN_VALUE

        fun empty(manager: AAInfoManager, strategy: RankStrategy): State =
            State(manager, IntDisjointSets(strategy))

        private fun restoreHeapInvariant(
            manager: AAInfoManager,
            state: IntDisjointSets,
            elementsToRemove: IntOpenHashSet,
        ) {
            while (true) {
                val replacements = mutableListOf<IntIntImmutablePair>()

                state.allElements().forEachInt { elementIdx ->
                    if (elementsToRemove.contains(elementIdx)) return@forEachInt

                    val fixedHeap = ensureHeapElementCorrect(elementIdx, state, manager)
                    if (fixedHeap == elementIdx) return@forEachInt

                    replacements += IntIntImmutablePair(elementIdx, fixedHeap)
                }

                if (replacements.isEmpty()) return

                for (replacement in replacements) {
                    elementsToRemove.add(replacement.leftInt())
                    state.union(replacement.leftInt(), replacement.rightInt())
                }
            }
        }

        private fun ensureHeapElementCorrect(
            element: Int,
            state: IntDisjointSets,
            manager: AAInfoManager,
            visitedElements: IntOpenHashSet? = null
        ): Int {
            if (!manager.isHeapAlias(element)) return element

            if (visitedElements != null && !visitedElements.add(element)) {
                // todo: consider another recursion break mechanism
                return element
            }

            val heapElement = manager.getHeapRefUnchecked(element)
            val heapInstanceRepr = state.find(heapElement.instance)

            val nextVisited = visitedElements ?: IntOpenHashSet()
            val correctInstance = ensureHeapElementCorrect(heapInstanceRepr, state, manager, nextVisited)

            if (correctInstance == heapElement.instance) return element

            return manager.replaceHeapInstance(element, correctInstance)
        }

        fun merge(manager: AAInfoManager, strategy: RankStrategy, states: List<ImmutableState>): State {
            val allElementParentRelations = mutableListOf<IntIntMutablePair>()
            states.forEach { s ->
                val stateDsu = (s as State).aliasGroups
                stateDsu.collectElementParentPairs(allElementParentRelations)
            }

            val result = IntDisjointSets(strategy)
            mergeUnionRelations(allElementParentRelations, result, manager)

            return State(manager, result)
        }

        private fun mergeUnionRelations(
            relations: List<IntIntMutablePair>,
            result: IntDisjointSets,
            manager: AAInfoManager
        ) {
            val removedElements = IntOpenHashSet()
            while (true) {
                var modified = false
                relations.forEach {
                    val status = result.union(it.leftInt(), it.rightInt())
                    modified = modified or status
                }

                if (!modified) break

                restoreHeapInvariant(manager, result, removedElements)

                relations.forEach { relation ->
                    val fixedLeft = ensureHeapElementCorrect(relation.leftInt(), result, manager)
                    val fixedRight = ensureHeapElementCorrect(relation.rightInt(), result, manager)

                    relation.left(fixedLeft)
                    relation.right(fixedRight)
                }
            }
            result.removeAll(removedElements)
        }
    }
}

fun State.allElements(): IntOpenHashSet {
    val result = IntOpenHashSet()
    result.addAll(allSetElements())

    val unprocessedHeapElement = IntArrayList()
    result.forEachInt {
        if (manager.isHeapAlias(it)) unprocessedHeapElement.add(it)
    }

    while (unprocessedHeapElement.isNotEmpty()) {
        val element = unprocessedHeapElement.removeInt(unprocessedHeapElement.lastIndex)
        val instance = manager.getHeapRefUnchecked(element).instance
        if (result.add(instance)) {
            if (manager.isHeapAlias(instance)) {
                unprocessedHeapElement.add(instance)
            }
        }
    }

    return result
}
