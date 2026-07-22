package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import it.unimi.dsi.fastutil.longs.LongOpenHashSet
import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
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

class BaseOnlyInitialFactAbstraction(
    private val manager: BaseOnlyApManager,
) : InitialFactAbstraction {
    private val perBase = Object2ObjectOpenHashMap<AccessPathBase, BaseState>()

    private class BaseState {
        val added = LongOpenHashSet()
        val excluded = IntOpenHashSet()
        val emitted = LongOpenHashSet()

        fun excludes(accessor: AccessorIdx): Boolean = excluded.excludesIdx(accessor)
    }

    override fun addAbstractedInitialFact(
        factAp: FinalFactAp,
        typeChecker: FactTypeChecker,
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        factAp as BaseOnlyFinalFactAp
        val state = perBase.getOrPut(factAp.base) { BaseState() }
        if (!state.added.add(factAp.access)) return emptyList()

        val out = ArrayList<Pair<InitialFactAp, FinalFactAp>>()
        abstractOne(factAp.base, factAp.access, state, out)
        return out
    }

    override fun registerNewInitialFact(
        factAp: InitialFactAp,
        typeChecker: FactTypeChecker,
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        factAp as BaseOnlyInitialFactAp
        val state = perBase.getOrPut(factAp.base) { BaseState() }

        var modified = false
        when (val ex = factAp.exclusions) {
            is ExclusionSet.Concrete -> ex.set.forEach {
                val idx = manager.interner.index(it)
                if (state.excluded.add(idx)) modified = true
            }
            ExclusionSet.Empty -> {}
            ExclusionSet.Universe -> error("Unexpected universe exclusion")
        }
        if (!modified) return emptyList()

        val out = ArrayList<Pair<InitialFactAp, FinalFactAp>>()
        for (added in state.added) abstractOne(factAp.base, added, state, out)
        return out
    }

    private fun abstractOne(
        base: AccessPathBase,
        added: BaseOnlyAccess,
        state: BaseState,
        out: MutableList<Pair<InitialFactAp, FinalFactAp>>,
    ) {
        abstractOneBranch(base, added, state, out)
    }

    private fun abstractOneBranch(
        base: AccessPathBase,
        added: BaseOnlyAccess,
        state: BaseState,
        out: MutableList<Pair<InitialFactAp, FinalFactAp>>,
    ) {
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
        core.forEach { accessor ->
            if (!stopped) {
                emit(
                    base, prefix, slotOfIdx(accessor), isAbstract = true, exact = false,
                    valueAccessorState = BaseOnlyValueAccessorState.Normal, state, out,
                )
                if (state.excludes(accessor)) {
                    prefix.add(accessor)
                } else {
                    stopped = true
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
            var committedStatic = NO_ACCESSOR
            var committedField = NO_ACCESSOR
            for (idx in prefix) {
                when {
                    idx.isStaticAccessor() -> committedStatic = idx
                    idx.isFieldAccessor() || idx == ELEMENT_ACCESSOR_IDX -> committedField = idx
                }
            }
            val abstractAccess = BaseOnlyAccessOps.abstractAt(committedStatic, committedField, apSlot)
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
        var committedStatic = NO_ACCESSOR
        var committedField = NO_ACCESSOR
        for (idx in prefix) {
            when {
                idx.isStaticAccessor() -> committedStatic = idx
                idx.isFieldAccessor() || idx == ELEMENT_ACCESSOR_IDX -> committedField = idx
            }
        }
        val apAccess = BaseOnlyAccessOps.abstractAt(committedStatic, committedField, apSlot)
        if (!state.emitted.add(apAccess)) return
        initialAccess = apAccess
        finalAccess = apAccess

        val initial = BaseOnlyInitialFactAp(manager, base, initialAccess, ExclusionSet.Empty)
        val final = BaseOnlyFinalFactAp(manager, base, finalAccess, ExclusionSet.Empty)
        out.add(initial to final)
    }
}
