package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.clean
import org.opentaint.dataflow.taint.Cleaner
import org.opentaint.dataflow.ap.ifds.access.forExclusions
import org.opentaint.dataflow.ap.ifds.tryAnyAccessorOrNull

data class AccessGraphFinalFactAp(
    override val base: AccessPathBase,
    override val access: AccessGraph,
    override val exclusions: ExclusionSet,
    val anyFieldCleanerEffects: AnyFieldCleanerEffects = AnyFieldCleanerEffects.Empty,
) : FinalFactAp, AccessGraphAccessorList {
    init {
        check(exclusions !is ExclusionSet.Universe || anyFieldCleanerEffects.isEmpty) {
            "Universe facts cannot carry cleaner effects"
        }
    }

    override val size: Int get() = access.size
    override val depth: Int get() = size

    override fun rebase(newBase: AccessPathBase): FinalFactAp =
        AccessGraphFinalFactAp(newBase, access, exclusions, anyFieldCleanerEffects)

    override fun exclude(accessor: Accessor): FinalFactAp {
        check(accessor !is AnyAccessor)
        return AccessGraphFinalFactAp(base, access, exclusions.add(accessor), anyFieldCleanerEffects)
    }

    override fun replaceExclusions(exclusions: ExclusionSet): FinalFactAp =
        AccessGraphFinalFactAp(
            base,
            access,
            exclusions,
            anyFieldCleanerEffects.takeUnless { exclusions is ExclusionSet.Universe }
                ?: AnyFieldCleanerEffects.Empty,
        )

    // Automata transports residual cleaner effects beside its graph.
    override fun abstractPart(): FinalFactAp =
        AccessGraphFinalFactAp(base, access.manager.emptyGraph(), exclusions, anyFieldCleanerEffects)

    override fun isAbstract(): Boolean =
        exclusions !is ExclusionSet.Universe && access.initialNodeIsFinal()

    override fun readAccessor(accessor: Accessor): FinalFactAp? = with(access.manager) {
        val graph = access.read(accessor.idx)
            ?: tryAnyAccessorOrNull(accessor) { access.read(anyAccessorIdx) }

        return graph?.let { AccessGraphFinalFactAp(base, it, exclusions, anyFieldCleanerEffects) }
    }

    override fun prependAccessor(accessor: Accessor): FinalFactAp = with(access.manager) {
        AccessGraphFinalFactAp(base, access.prepend(accessor.idx), exclusions, anyFieldCleanerEffects)
    }

    override fun clearAccessor(accessor: Accessor): FinalFactAp? = with(access.manager) {
        return access.clear(accessor.idx)?.let { AccessGraphFinalFactAp(base, it, exclusions, anyFieldCleanerEffects) }
    }

    override fun clean(cleaner: Cleaner): FinalFactAp.CleanResult =
        clean(cleaner, ::cleanAnyField)

    override fun cleanExactAndAnyField(
        mark: TaintMarkAccessor,
    ): FinalFactAp.CleanResult {
        val cleaned = with(access.manager) { access.cleanExactAndAnyField(mark.idx) }
            ?: return FinalFactAp.CleanResult(emptyList(), removedAlternative = true)
        if (cleaned === access) {
            return FinalFactAp.CleanResult(listOf(this), removedAlternative = false)
        }
        return FinalFactAp.CleanResult(
            listOf(AccessGraphFinalFactAp(base, cleaned, exclusions, anyFieldCleanerEffects)),
            removedAlternative = true,
        )
    }

    private fun cleanAnyField(
        mark: TaintMarkAccessor,
    ): FinalFactAp.CleanResult {
        val cleaned = with(access.manager) { access.cleanAnyField(mark.idx) }
            ?: return FinalFactAp.CleanResult(emptyList(), removedAlternative = true)
        val cleanedEffects = anyFieldCleanerEffects.add(mark).forExclusions(exclusions)
        return FinalFactAp.CleanResult(
            survivingFacts = listOf(
                AccessGraphFinalFactAp(
                    base,
                    cleaned,
                    exclusions,
                    cleanedEffects,
                )
            ),
            removedAlternative = false,
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

    override fun abstractOnly(): FinalFactAp =
        AccessGraphFinalFactAp(base, access.manager.emptyGraph(), exclusions)

    data class Delta(
        override val access: AccessGraph,
        val anyFieldCleanerEffects: AnyFieldCleanerEffects,
    ) : FinalFactAp.Delta, AccessGraphAccessorList {
        override val isEmpty: Boolean get() = access.isEmpty()

        override fun readAccessor(accessor: Accessor): FinalFactAp.Delta? = with(access.manager) {
            val newGraph = access.read(accessor.idx)
                ?: tryAnyAccessorOrNull(accessor) { access.read(anyAccessorIdx) }

            return newGraph?.let { Delta(it, anyFieldCleanerEffects) }
        }

        override fun isAbstract(): Boolean = access.initialNodeIsFinal()
    }

    override fun delta(other: InitialFactAp): List<FinalFactAp.Delta> {
        other as AccessGraphInitialFactAp
        if (base != other.base) return emptyList()

        return access.delta(other.access).mapNotNull { delta ->
            val filteredDelta = delta
                .filter(other.exclusions)
                ?.enforceAnyFieldCleaners(other.anyFieldCleanerEffects, keepInitialLevel = other.access.isEmpty())
                ?: return@mapNotNull null
            Delta(filteredDelta, anyFieldCleanerEffects)
        }
    }

    override fun hasEmptyDelta(other: InitialFactAp): Boolean {
        other as AccessGraphInitialFactAp
        if (base != other.base) return false

        return access.containsAll(other.access)
    }

    override fun concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp? {
        delta as Delta
        val composedEffects = (anyFieldCleanerEffects then delta.anyFieldCleanerEffects)
            .forExclusions(exclusions)
        if (delta.isEmpty) {
            return AccessGraphFinalFactAp(base, access, exclusions, composedEffects)
        }

        val filter = access.manager.createFilter(access, typeChecker)
        val filteredDelta = delta.access.filter(filter) ?: return null

        if (access.isEmpty()) {
            return AccessGraphFinalFactAp(
                base, filteredDelta, exclusions, composedEffects
            )
        }

        val concatenatedGraph = access.concat(filteredDelta)
        return AccessGraphFinalFactAp(
            base, concatenatedGraph, exclusions, composedEffects
        )
    }

    override fun filterFact(filter: FactTypeChecker.FactApFilter): FinalFactAp? =
        access.filter(filter)?.let { AccessGraphFinalFactAp(base, it, exclusions, anyFieldCleanerEffects) }

    override fun filterFact(filter: FactTypeChecker.FactCompatibilityFilter): FinalFactAp? =
        access.filter(filter)?.let { AccessGraphFinalFactAp(base, it, exclusions, anyFieldCleanerEffects) }

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
