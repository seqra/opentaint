package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.DeepCleanEffects
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

data class AccessGraphInitialFactAp(
    override val base: AccessPathBase,
    override val access: AccessGraph,
    override val exclusions: ExclusionSet,
    override val deepCleanEffects: DeepCleanEffects = DeepCleanEffects.Empty,
) : InitialFactAp, AccessGraphAccessorList {
    init {
        FactFlowState(exclusions, deepCleanEffects)
    }

    override val size: Int get() = access.size
    override val depth: Int get() = size

    override fun rebase(newBase: AccessPathBase): InitialFactAp =
        AccessGraphInitialFactAp(newBase, access, exclusions, deepCleanEffects)

    override fun isAbstract(): Boolean =
        exclusions !is ExclusionSet.Universe && access.initialNodeIsFinal()

    override fun exclude(accessor: Accessor): InitialFactAp {
        check(accessor !is AnyAccessor)
        return AccessGraphInitialFactAp(base, access, exclusions.add(accessor), deepCleanEffects)
    }

    override fun replaceExclusions(exclusions: ExclusionSet): InitialFactAp =
        replaceFlowState(flowState.withExclusions(exclusions))

    override fun replaceFlowState(flowState: FactFlowState): InitialFactAp =
        AccessGraphInitialFactAp(base, access, flowState.exclusions, flowState.deepCleanEffects)

    override fun readAccessor(accessor: Accessor): InitialFactAp? = with(access.manager) {
        check(accessor !is AnyAccessor)
        return access.read(accessor.idx)?.let {
            AccessGraphInitialFactAp(base, it, exclusions, deepCleanEffects)
        }
    }

    override fun prependAccessor(accessor: Accessor): InitialFactAp = with(access.manager) {
        check(accessor !is AnyAccessor)
        return AccessGraphInitialFactAp(base, access.prepend(accessor.idx), exclusions, deepCleanEffects)
    }

    override fun clearAccessor(accessor: Accessor): InitialFactAp? = with(access.manager) {
        check(accessor !is AnyAccessor)
        return access.clear(accessor.idx)?.let {
            AccessGraphInitialFactAp(base, it, exclusions, deepCleanEffects)
        }
    }

    data class Delta(
        override val access: AccessGraph,
        override val deepCleanEffects: DeepCleanEffects,
    ) : InitialFactAp.Delta, AccessGraphAccessorList {
        override val isEmpty: Boolean get() = access.isEmpty()

        override fun concat(other: InitialFactAp.Delta): InitialFactAp.Delta {
            other as Delta

            return Delta(access.concat(other.access), deepCleanEffects then other.deepCleanEffects)
        }

        override fun readAccessor(accessor: Accessor): InitialFactAp.Delta? = with(access.manager) {
            val newGraph = access.read(accessor.idx) ?: return@with null
            return Delta(newGraph, deepCleanEffects)
        }

        override fun isAbstract(): Boolean = access.initialNodeIsFinal()
    }

    override fun splitDelta(other: FinalFactAp): List<Pair<InitialFactAp, InitialFactAp.Delta>> {
        other as AccessGraphFinalFactAp
        if (base != other.base) return emptyList()

        if (other.access.isEmpty()) {
            val filteredDelta = this.access
                .filter(other.exclusions)
                ?.filterDeep(other.deepCleanEffects, keepInitialLevel = true)
                ?: return emptyList()

            val emptyFact = AccessGraphInitialFactAp(
                base, access.manager.emptyGraph(), exclusions, deepCleanEffects
            )
            return listOf(emptyFact to Delta(filteredDelta, deepCleanEffects))
        }

        return access.splitDelta(other.access).mapNotNull { (matchedAccess, delta) ->
            val filteredDelta = delta
                .filter(other.exclusions)
                ?.filterDeep(other.deepCleanEffects, keepInitialLevel = matchedAccess.isEmpty())
                ?: return@mapNotNull null

            val matchedFact = AccessGraphInitialFactAp(base, matchedAccess, exclusions, deepCleanEffects)
            matchedFact to Delta(filteredDelta, deepCleanEffects)
        }
    }

    override fun concat(delta: InitialFactAp.Delta): InitialFactAp {
        delta as Delta
        val composedState = flowState then FactFlowState(ExclusionSet.Empty, delta.deepCleanEffects)
        if (delta.isEmpty) return replaceFlowState(composedState)

        val concatenatedGraph = access.concat(delta.access)
        return AccessGraphInitialFactAp(
            base, concatenatedGraph, composedState.exclusions, composedState.deepCleanEffects
        )
    }

    override fun contains(factAp: InitialFactAp): Boolean {
        factAp as AccessGraphInitialFactAp

        if (base != factAp.base) return false
        return access.containsAll(factAp.access)
    }

    override fun compatibilityFilter(typeChecker: FactTypeChecker): FactTypeChecker.FactCompatibilityFilter =
        access.manager.createCompatibilityFilter(access, typeChecker)
}
