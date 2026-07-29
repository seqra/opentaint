package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.AnyFieldMarkExclusions
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.clean
import org.opentaint.dataflow.taint.Cleaner
import org.opentaint.dataflow.ap.ifds.access.forExclusions
import org.opentaint.dataflow.ap.ifds.tryAnyAccessorOrNull

data class AccessGraphFinalFactAp(
    override val base: AccessPathBase,
    override val access: AccessGraph,
    override val exclusions: ExclusionSet,
    val anyFieldMarkExclusions: AnyFieldMarkExclusions = AnyFieldMarkExclusions.Empty,
) : FinalFactAp, AccessGraphAccessorList {
    init {
        check(exclusions !is ExclusionSet.Universe || anyFieldMarkExclusions.isEmpty) {
            "Universe facts cannot carry AnyField mark exclusions"
        }
    }

    override val size: Int get() = access.size
    override val depth: Int get() = size

    override fun rebase(newBase: AccessPathBase): FinalFactAp =
        AccessGraphFinalFactAp(newBase, access, exclusions, anyFieldMarkExclusions)

    override fun exclude(accessor: Accessor): FinalFactAp {
        check(accessor !is AnyAccessor)
        return AccessGraphFinalFactAp(base, access, exclusions.add(accessor), anyFieldMarkExclusions)
    }

    override fun replaceExclusions(exclusions: ExclusionSet): FinalFactAp =
        AccessGraphFinalFactAp(
            base,
            access,
            exclusions,
            anyFieldMarkExclusions.takeUnless { exclusions is ExclusionSet.Universe }
                ?: AnyFieldMarkExclusions.Empty,
        )

    // Automata transports root AnyField mark exclusions beside its graph.
    override fun abstractPart(): FinalFactAp =
        AccessGraphFinalFactAp(base, access.manager.emptyGraph(), exclusions, anyFieldMarkExclusions)

    override fun isAbstract(): Boolean =
        exclusions !is ExclusionSet.Universe && access.initialNodeIsFinal()

    override fun readAccessor(accessor: Accessor): FinalFactAp? = with(access.manager) {
        val graph = access.read(accessor.idx)
            ?: tryAnyAccessorOrNull(accessor) { access.read(anyAccessorIdx) }

        return graph?.let { AccessGraphFinalFactAp(base, it, exclusions, anyFieldMarkExclusions) }
    }

    override fun prependAccessor(accessor: Accessor): FinalFactAp = with(access.manager) {
        AccessGraphFinalFactAp(base, access.prepend(accessor.idx), exclusions, anyFieldMarkExclusions)
    }

    override fun clearAccessor(accessor: Accessor): FinalFactAp? = with(access.manager) {
        return access.clear(accessor.idx)?.let { AccessGraphFinalFactAp(base, it, exclusions, anyFieldMarkExclusions) }
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
            listOf(AccessGraphFinalFactAp(base, cleaned, exclusions, anyFieldMarkExclusions)),
            removedAlternative = true,
        )
    }

    private fun cleanAnyField(
        mark: TaintMarkAccessor,
    ): FinalFactAp.CleanResult {
        val cleaned = with(access.manager) { access.cleanAnyField(mark.idx) }
            ?: return FinalFactAp.CleanResult(emptyList(), removedAlternative = true)
        val cleanedAnyFieldMarkExclusions = with(access.manager) {
            anyFieldMarkExclusions.add(mark.idx)
        }.forExclusions(exclusions)
        return FinalFactAp.CleanResult(
            survivingFacts = listOf(
                AccessGraphFinalFactAp(
                    base,
                    cleaned,
                    exclusions,
                    cleanedAnyFieldMarkExclusions,
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
        val anyFieldMarkExclusions: AnyFieldMarkExclusions,
    ) : FinalFactAp.Delta, AccessGraphAccessorList {
        override val isEmpty: Boolean get() = access.isEmpty()

        override fun readAccessor(accessor: Accessor): FinalFactAp.Delta? = with(access.manager) {
            val newGraph = access.read(accessor.idx)
                ?: tryAnyAccessorOrNull(accessor) { access.read(anyAccessorIdx) }

            return newGraph?.let { Delta(it, anyFieldMarkExclusions) }
        }

        override fun isAbstract(): Boolean = access.initialNodeIsFinal()
    }

    override fun delta(other: InitialFactAp): List<FinalFactAp.Delta> {
        other as AccessGraphInitialFactAp
        if (base != other.base) return emptyList()

        return access.delta(other.access).mapNotNull { delta ->
            val filteredDelta = delta
                .filter(other.exclusions)
                ?.enforceAnyFieldMarkExclusions(
                    anyFieldMarkExclusions,
                    keepInitialLevel = other.access.isEmpty(),
                )
                ?: return@mapNotNull null
            Delta(filteredDelta, anyFieldMarkExclusions)
        }
    }

    override fun hasEmptyDelta(other: InitialFactAp): Boolean {
        other as AccessGraphInitialFactAp
        if (base != other.base) return false

        return access.containsAll(other.access)
    }

    override fun concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp? {
        delta as Delta
        val composedAnyFieldMarkExclusions = (anyFieldMarkExclusions then delta.anyFieldMarkExclusions)
            .forExclusions(exclusions)
        if (delta.isEmpty) {
            return AccessGraphFinalFactAp(base, access, exclusions, composedAnyFieldMarkExclusions)
        }

        val filter = access.manager.createFilter(access, typeChecker)
        val filteredDelta = delta.access.filter(filter) ?: return null

        if (access.isEmpty()) {
            return AccessGraphFinalFactAp(
                base, filteredDelta, exclusions, composedAnyFieldMarkExclusions
            )
        }

        val concatenatedGraph = access.concat(filteredDelta)
        return AccessGraphFinalFactAp(
            base, concatenatedGraph, exclusions, composedAnyFieldMarkExclusions
        )
    }

    override fun filterFact(filter: FactTypeChecker.FactApFilter): FinalFactAp? =
        access.filter(filter)?.let { AccessGraphFinalFactAp(base, it, exclusions, anyFieldMarkExclusions) }

    override fun filterFact(filter: FactTypeChecker.FactCompatibilityFilter): FinalFactAp? =
        access.filter(filter)?.let { AccessGraphFinalFactAp(base, it, exclusions, anyFieldMarkExclusions) }

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
