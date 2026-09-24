package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap
import it.unimi.dsi.fastutil.longs.Long2LongOpenHashMap
import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap
import it.unimi.dsi.fastutil.longs.LongOpenHashSet
import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAbstraction
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.VALUE_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTypeInfoAccessor

class BaseOnlyInitialFactAbstraction(
    private val manager: BaseOnlyApManager,
) : InitialFactAbstraction {
    private val perBase = Object2ObjectOpenHashMap<AccessPathBase, BaseState>()

    private inner class BaseState {
        val added = LongOpenHashSet()
        val emitted = LongOpenHashSet()
        val knownExclusionsByPattern = Long2ObjectOpenHashMap<BaseOnlyExclusionAccessorSet>()
        val factsByExclusion = Int2ObjectOpenHashMap<LongOpenHashSet>()
        val blockedAtByFact = Long2LongOpenHashMap()
        val concreteTypeBlockerByFact = Long2IntOpenHashMap().apply { defaultReturnValue(NO_ACCESSOR) }

        fun addExclusionsAndFindUnblockedAccessors(
            pattern: BaseOnlyAccess,
            exclusions: Set<Accessor>,
        ): IntArrayList? {
            val compactExclusions = BaseOnlyExclusionAccessorSet.from(manager, exclusions)
            val knownExclusions = knownExclusionsByPattern[pattern]

            if (knownExclusions == null) {
                if (compactExclusions.isEmpty()) return null

                knownExclusionsByPattern[pattern] = compactExclusions
                return newlyExcludedBlockedAccessors(compactExclusions, previouslyExcluded = null)
            }

            val union = knownExclusions.unionIfChanged(compactExclusions) ?: return null

            knownExclusionsByPattern[pattern] = union
            return newlyExcludedBlockedAccessors(compactExclusions, knownExclusions)
        }

        fun excludes(blockedAt: BaseOnlyAccess, accessor: AccessorIdx): Boolean {
            val typeGroupMatches = accessor.isTypeInfoAccessor()
            val iterator = knownExclusionsByPattern.long2ObjectEntrySet().fastIterator()
            while (iterator.hasNext()) {
                val entry = iterator.next()
                if (!exclusionPatternCovers(entry.longKey, blockedAt)) continue
                val exclusions = entry.value
                if (exclusions.containsIndex(accessor)) return true
                if (typeGroupMatches && exclusions.containsIndex(TYPE_INFO_GROUP_ACCESSOR_IDX)) return true
            }
            return false
        }

        fun registerBlockedFact(access: BaseOnlyAccess, blockedAt: BaseOnlyAccess, accessor: AccessorIdx) {
            check(!blockedAtByFact.containsKey(access))
            blockedAtByFact.put(access, blockedAt)
            check(factsByExclusion.computeIfAbsent(accessor) { LongOpenHashSet() }.add(access))
            if (accessor.isTypeInfoAccessor() && accessor != TYPE_INFO_GROUP_ACCESSOR_IDX) {
                check(concreteTypeBlockerByFact.put(access, accessor) == NO_ACCESSOR)
                check(
                    factsByExclusion
                        .computeIfAbsent(TYPE_INFO_GROUP_ACCESSOR_IDX) { LongOpenHashSet() }
                        .add(access)
                )
            }
        }

        fun takeFactsUnblockedBy(accessor: AccessorIdx, pattern: BaseOnlyAccess): LongOpenHashSet? {
            val candidates = factsByExclusion[accessor] ?: return null
            val unblocked = LongOpenHashSet()
            val candidateIterator = candidates.iterator()
            while (candidateIterator.hasNext()) {
                val access = candidateIterator.nextLong()
                val blockedAt = blockedAtByFact.get(access)
                if (!exclusionPatternCovers(pattern, blockedAt)) continue

                candidateIterator.remove()
                unblocked.add(access)
                blockedAtByFact.remove(access)
                val concreteTypeBlocker = concreteTypeBlockerByFact.remove(access)
                if (accessor == TYPE_INFO_GROUP_ACCESSOR_IDX && concreteTypeBlocker != NO_ACCESSOR) {
                    factsByExclusion[concreteTypeBlocker]?.remove(access)
                } else if (concreteTypeBlocker != NO_ACCESSOR) {
                    factsByExclusion[TYPE_INFO_GROUP_ACCESSOR_IDX]?.remove(access)
                }
            }
            if (candidates.isEmpty()) factsByExclusion.remove(accessor)
            return unblocked.takeUnless { it.isEmpty() }
        }

        private fun newlyExcludedBlockedAccessors(
            exclusions: BaseOnlyExclusionAccessorSet,
            previouslyExcluded: BaseOnlyExclusionAccessorSet?,
        ): IntArrayList? {
            var result: IntArrayList? = null
            val iterator = factsByExclusion.keys.iterator()
            while (iterator.hasNext()) {
                val accessor = iterator.nextInt()
                if (exclusions.containsIndex(accessor) && previouslyExcluded?.containsIndex(accessor) != true) {
                    val matches = result ?: IntArrayList().also { result = it }
                    matches.add(accessor)
                }
            }
            return result
        }

        private fun exclusionPatternCovers(pattern: BaseOnlyAccess, blockedAt: BaseOnlyAccess): Boolean =
            pattern == ABSTRACT_EMPTY_ACCESS || BaseOnlyAccessOps.containsAccess(pattern, blockedAt)
    }

    private data class Blocker(val accessor: AccessorIdx, val blockedAt: BaseOnlyAccess)

    override fun addAbstractedInitialFact(
        factAp: FinalFactAp,
        typeChecker: FactTypeChecker,
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        factAp as BaseOnlyFinalFactAp
        val state = perBase.getOrPut(factAp.base) { BaseState() }
        if (!state.added.add(factAp.access)) return emptyList()

        val out = ArrayList<Pair<InitialFactAp, FinalFactAp>>()
        abstractAndIndex(factAp.base, factAp.access, state, out)
        return out
    }

    override fun registerNewInitialFact(
        factAp: InitialFactAp,
        typeChecker: FactTypeChecker,
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        factAp as BaseOnlyInitialFactAp
        val state = perBase.getOrPut(factAp.base) { BaseState() }

        val unblockedAccessors = when (val ex = factAp.exclusions) {
            is ExclusionSet.Concrete -> state.addExclusionsAndFindUnblockedAccessors(
                factAp.access,
                ex.set,
            )
            ExclusionSet.Empty -> null
            ExclusionSet.Universe -> error("Unexpected universe exclusion")
        }
        if (unblockedAccessors == null) return emptyList()

        val out = ArrayList<Pair<InitialFactAp, FinalFactAp>>()
        val exclusionIterator = unblockedAccessors.iterator()
        while (exclusionIterator.hasNext()) {
            val accessor = exclusionIterator.nextInt()
            val unblocked = state.takeFactsUnblockedBy(accessor, factAp.access) ?: continue
            val unblockedIterator = unblocked.iterator()
            while (unblockedIterator.hasNext()) {
                abstractAndIndex(factAp.base, unblockedIterator.nextLong(), state, out)
            }
        }
        return out
    }

    private fun abstractAndIndex(
        base: AccessPathBase,
        added: BaseOnlyAccess,
        state: BaseState,
        out: MutableList<Pair<InitialFactAp, FinalFactAp>>,
    ) {
        val blocker = abstractOneBranch(base, added, state, out)
        if (blocker != null) state.registerBlockedFact(added, blocker.blockedAt, blocker.accessor)
    }

    private fun abstractOneBranch(
        base: AccessPathBase,
        added: BaseOnlyAccess,
        state: BaseState,
        out: MutableList<Pair<InitialFactAp, FinalFactAp>>,
    ): Blocker? {
        val prefix = ArrayList<Int>(3)
        var stopped = false
        val core = buildList {
            if (added.staticIdx >= 0) add(added.staticIdx)
            if (added.fieldIdx >= 0) add(added.fieldIdx)
            if (added.hasSemanticMark && added.valueAccessorState == BaseOnlyValueAccessorState.Value) {
                add(if (added.hasTypeInfoSuffix) TYPE_INFO_GROUP_ACCESSOR_IDX else VALUE_ACCESSOR_IDX)
            }
            if (added.suffixIdx >= 0 && added.suffixIdx != FINAL_ACCESSOR_IDX) add(added.suffixIdx)
        }
        var blocker: Blocker? = null
        core.forEach { accessor ->
            if (!stopped) {
                val blockedAt = abstractAccess(prefix, slotOfIdx(accessor))
                emit(
                    base, prefix, slotOfIdx(accessor), isAbstract = true, exact = false,
                    valueAccessorState = BaseOnlyValueAccessorState.Normal, state, out,
                )
                if (state.excludes(blockedAt, accessor)) {
                    prefix.add(accessor)
                } else {
                    stopped = true
                    blocker = Blocker(accessor, blockedAt)
                }
            }
        }
        if (!stopped) {
            if (added.hasAp) {
                emit(
                    base, prefix, apSlot = added.apSlot, isAbstract = true, exact = false,
                    valueAccessorState = BaseOnlyValueAccessorState.Normal, state, out,
                )
            } else {
                emit(
                    base, prefix, apSlot = 2, isAbstract = false, exact = true,
                    valueAccessorState = added.valueAccessorState, state, out,
                )
            }
        }
        return blocker
    }

    private fun abstractAccess(prefix: List<Int>, apSlot: Int): BaseOnlyAccess {
        var committedStatic = NO_ACCESSOR
        var committedField = NO_ACCESSOR
        for (idx in prefix) {
            when {
                idx.isStaticAccessor() -> committedStatic = idx
                idx.isFieldAccessor() || idx == ELEMENT_ACCESSOR_IDX -> committedField = idx
            }
        }
        return BaseOnlyAccessOps.abstractAt(committedStatic, committedField, apSlot)
    }

    private fun emit(
        base: AccessPathBase,
        prefix: List<Int>,
        apSlot: Int,
        isAbstract: Boolean,
        exact: Boolean,
        valueAccessorState: BaseOnlyValueAccessorState,
        state: BaseState,
        out: MutableList<Pair<InitialFactAp, FinalFactAp>>,
    ) {
        if (exact) {
            val abstractAccess = abstractAccess(prefix, apSlot)
            if (state.emitted.add(abstractAccess)) {
                out.add(
                    BaseOnlyInitialFactAp(manager, base, abstractAccess, ExclusionSet.Empty)
                        to BaseOnlyFinalFactAp(manager, base, abstractAccess, ExclusionSet.Empty)
                )
            }
            var concreteAccess = BaseOnlyAccessOps.build(
                (prefix + FINAL_ACCESSOR_IDX).toIntArray(),
                isAbstract = false,
            )
            if (concreteAccess.hasSemanticMark) concreteAccess = concreteAccess.withValueAccessorState(valueAccessorState)
            if (state.emitted.add(concreteAccess)) {
                out.add(
                    BaseOnlyInitialFactAp(manager, base, concreteAccess, ExclusionSet.Empty)
                        to BaseOnlyFinalFactAp(manager, base, concreteAccess, ExclusionSet.Empty)
                )
            }
            return
        }

        val initialAccess: BaseOnlyAccess
        val finalAccess: BaseOnlyAccess
        val apAccess = abstractAccess(prefix, apSlot)
        if (!state.emitted.add(apAccess)) return
        initialAccess = apAccess
        finalAccess = apAccess

        val initial = BaseOnlyInitialFactAp(manager, base, initialAccess, ExclusionSet.Empty)
        val final = BaseOnlyFinalFactAp(manager, base, finalAccess, ExclusionSet.Empty)
        out.add(initial to final)
    }
}
