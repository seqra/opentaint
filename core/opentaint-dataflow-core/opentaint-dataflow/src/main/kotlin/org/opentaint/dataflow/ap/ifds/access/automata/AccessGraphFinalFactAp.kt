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
import org.opentaint.dataflow.ap.ifds.tryAnyAccessorOrNull

data class AccessGraphFinalFactAp(
    override val base: AccessPathBase,
    override val access: AccessGraph,
    override val exclusions: ExclusionSet,
    override val deepCleanEffects: DeepCleanEffects = DeepCleanEffects.Empty,
) : FinalFactAp, AccessGraphAccessorList {
    init {
        FactFlowState(exclusions, deepCleanEffects)
    }

    override val size: Int get() = access.size
    override val depth: Int get() = size

    override fun rebase(newBase: AccessPathBase): FinalFactAp =
        AccessGraphFinalFactAp(newBase, access, exclusions, deepCleanEffects)

    override fun exclude(accessor: Accessor): FinalFactAp {
        check(accessor !is AnyAccessor)
        return AccessGraphFinalFactAp(base, access, exclusions.add(accessor), deepCleanEffects)
    }

    override fun replaceExclusions(exclusions: ExclusionSet): FinalFactAp =
        replaceFlowState(flowState.withExclusions(exclusions))

    override fun replaceFlowState(flowState: FactFlowState): FinalFactAp =
        AccessGraphFinalFactAp(base, access, flowState.exclusions, flowState.deepCleanEffects)

    // Automata transports residual cleaner effects beside its graph.
    override fun abstractPart(): FinalFactAp =
        AccessGraphFinalFactAp(base, access.manager.emptyGraph(), exclusions, deepCleanEffects)

    override fun isAbstract(): Boolean =
        exclusions !is ExclusionSet.Universe && access.initialNodeIsFinal()

    override fun readAccessor(accessor: Accessor): FinalFactAp? = with(access.manager) {
        val graph = access.read(accessor.idx)
            ?: tryAnyAccessorOrNull(accessor) { access.read(anyAccessorIdx) }

        return graph?.let { AccessGraphFinalFactAp(base, it, exclusions, deepCleanEffects) }
    }

    override fun prependAccessor(accessor: Accessor): FinalFactAp = with(access.manager) {
        AccessGraphFinalFactAp(base, access.prepend(accessor.idx), exclusions, deepCleanEffects)
    }

    override fun clearAccessor(accessor: Accessor): FinalFactAp? = with(access.manager) {
        return access.clear(accessor.idx)?.let { AccessGraphFinalFactAp(base, it, exclusions, deepCleanEffects) }
    }

    override fun deepClean(mark: org.opentaint.dataflow.ap.ifds.TaintMarkAccessor): FinalFactAp.DeepCleanResult {
        val cleaned = with(access.manager) { access.deepClean(mark.idx) }
            ?: return FinalFactAp.DeepCleanResult.RemovedCompletely
        val cleanedState = flowState.cleanDeep(mark)
        return FinalFactAp.DeepCleanResult.Cleaned(
            AccessGraphFinalFactAp(
                base,
                cleaned,
                cleanedState.exclusions,
                cleanedState.deepCleanEffects,
            )
        )
    }

    override fun removeAbstraction(): FinalFactAp? {
        /**
         * Automata is at an abstraction point when its
         * initial node and final node are the same node.
         * If we remove the abstraction point we remove the final and initial nodes.
         * So, we remove entire automata.
         * */
        return null
    }

    data class Delta(
        override val access: AccessGraph,
        override val deepCleanEffects: DeepCleanEffects,
    ) : FinalFactAp.Delta, AccessGraphAccessorList {
        override val isEmpty: Boolean get() = access.isEmpty()

        override fun readAccessor(accessor: Accessor): FinalFactAp.Delta? = with(access.manager) {
            val newGraph = access.read(accessor.idx)
                ?: tryAnyAccessorOrNull(accessor) { access.read(anyAccessorIdx) }

            return newGraph?.let { Delta(it, deepCleanEffects) }
        }

        override fun isAbstract(): Boolean = access.initialNodeIsFinal()
    }

    override fun delta(other: InitialFactAp): List<FinalFactAp.Delta> {
        other as AccessGraphInitialFactAp
        if (base != other.base) return emptyList()

        return access.delta(other.access).mapNotNull { delta ->
            val filteredDelta = delta
                .filter(other.exclusions)
                ?.filterDeep(other.deepCleanEffects, keepInitialLevel = other.access.isEmpty())
                ?: return@mapNotNull null
            Delta(filteredDelta, deepCleanEffects)
        }
    }

    override fun hasEmptyDelta(other: InitialFactAp): Boolean {
        other as AccessGraphInitialFactAp
        if (base != other.base) return false

        return access.containsAll(other.access)
    }

    override fun concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp? {
        delta as Delta
        val composedState = flowState then FactFlowState(ExclusionSet.Empty, delta.deepCleanEffects)
        if (delta.isEmpty) return replaceFlowState(composedState)

        val filter = access.manager.createFilter(access, typeChecker)
        val filteredDelta = delta.access.filter(filter) ?: return null

        if (access.isEmpty()) {
            return AccessGraphFinalFactAp(
                base, filteredDelta, composedState.exclusions, composedState.deepCleanEffects
            )
        }

        val concatenatedGraph = access.concat(filteredDelta)
        return AccessGraphFinalFactAp(
            base, concatenatedGraph, composedState.exclusions, composedState.deepCleanEffects
        )
    }

    override fun filterFact(filter: FactTypeChecker.FactApFilter): FinalFactAp? =
        access.filter(filter)?.let { AccessGraphFinalFactAp(base, it, exclusions, deepCleanEffects) }

    override fun filterFact(filter: FactTypeChecker.FactCompatibilityFilter): FinalFactAp? =
        access.filter(filter)?.let { AccessGraphFinalFactAp(base, it, exclusions, deepCleanEffects) }

    override fun contains(factAp: InitialFactAp): Boolean {
        factAp as AccessGraphInitialFactAp

        if (base != factAp.base) return false
        return access.containsAll(factAp.access)
    }

    override fun equalTo(factAp: InitialFactAp): Boolean {
        factAp as AccessGraphInitialFactAp

        if (base != factAp.base) return false
        return access == factAp.access
    }
}
