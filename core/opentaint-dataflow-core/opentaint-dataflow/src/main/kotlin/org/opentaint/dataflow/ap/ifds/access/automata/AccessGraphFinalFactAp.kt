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
) : FinalFactAp, AccessGraphAccessorList {
    val anyFieldMarkExclusions: AnyFieldMarkExclusions
        get() = access.anyFieldMarkExclusions

    init {
        check(exclusions !is ExclusionSet.Universe || anyFieldMarkExclusions.isEmpty) {
            "Universe facts cannot carry AnyField mark exclusions"
        }
    }

    override val size: Int get() = access.size
    override val depth: Int get() = size

    override fun rebase(newBase: AccessPathBase): FinalFactAp =
        AccessGraphFinalFactAp(newBase, access, exclusions)

    override fun exclude(accessor: Accessor): FinalFactAp {
        check(accessor !is AnyAccessor)
        return AccessGraphFinalFactAp(base, access, exclusions.add(accessor))
    }

    override fun replaceExclusions(exclusions: ExclusionSet): FinalFactAp =
        AccessGraphFinalFactAp(base, access.forExclusions(exclusions), exclusions)

    // Cleaner state belongs to the graph value even when its access-path shape is empty.
    override fun abstractPart(): FinalFactAp =
        AccessGraphFinalFactAp(
            base,
            access.manager.emptyGraph().withAnyFieldMarkExclusions(anyFieldMarkExclusions),
            exclusions,
        )

    override fun isAbstract(): Boolean =
        exclusions !is ExclusionSet.Universe && access.initialNodeIsFinal()

    override fun readAccessor(accessor: Accessor): FinalFactAp? = with(access.manager) {
        val graph = access.read(accessor.idx)
            ?: tryAnyAccessorOrNull(accessor) { access.read(anyAccessorIdx) }

        return graph?.let { AccessGraphFinalFactAp(base, it, exclusions) }
    }

    override fun prependAccessor(accessor: Accessor): FinalFactAp = with(access.manager) {
        AccessGraphFinalFactAp(base, access.prepend(accessor.idx), exclusions)
    }

    override fun clearAccessor(accessor: Accessor): FinalFactAp? = with(access.manager) {
        return access.clear(accessor.idx)?.let { AccessGraphFinalFactAp(base, it, exclusions) }
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
            listOf(AccessGraphFinalFactAp(base, cleaned, exclusions)),
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
                    cleaned.withAnyFieldMarkExclusions(cleanedAnyFieldMarkExclusions),
                    exclusions,
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
    ) : FinalFactAp.Delta, AccessGraphAccessorList {
        val anyFieldMarkExclusions: AnyFieldMarkExclusions
            get() = access.anyFieldMarkExclusions

        override val isEmpty: Boolean get() = access.isEmpty()

        override fun readAccessor(accessor: Accessor): FinalFactAp.Delta? = with(access.manager) {
            val newGraph = access.read(accessor.idx)
                ?: tryAnyAccessorOrNull(accessor) { access.read(anyAccessorIdx) }

            return newGraph?.let(::Delta)
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
            Delta(filteredDelta.withAnyFieldMarkExclusions(anyFieldMarkExclusions))
        }
    }

    override fun hasEmptyDelta(other: InitialFactAp): Boolean {
        other as AccessGraphInitialFactAp
        if (base != other.base) return false

        return access.containsAllAccessPaths(other.access)
    }

    override fun concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp? {
        delta as Delta
        val composedAnyFieldMarkExclusions = (anyFieldMarkExclusions then delta.anyFieldMarkExclusions)
            .forExclusions(exclusions)
        if (delta.isEmpty) {
            return AccessGraphFinalFactAp(
                base,
                access.withAnyFieldMarkExclusions(composedAnyFieldMarkExclusions),
                exclusions,
            )
        }

        val filter = access.manager.createFilter(access, typeChecker)
        val filteredDelta = delta.access.filter(filter) ?: return null

        if (access.isEmpty()) {
            return AccessGraphFinalFactAp(
                base,
                filteredDelta.withAnyFieldMarkExclusions(composedAnyFieldMarkExclusions),
                exclusions,
            )
        }

        val concatenatedGraph = access.concat(filteredDelta)
        return AccessGraphFinalFactAp(
            base,
            concatenatedGraph.withAnyFieldMarkExclusions(composedAnyFieldMarkExclusions),
            exclusions,
        )
    }

    override fun filterFact(filter: FactTypeChecker.FactApFilter): FinalFactAp? =
        access.filter(filter)?.let { AccessGraphFinalFactAp(base, it, exclusions) }

    override fun filterFact(filter: FactTypeChecker.FactCompatibilityFilter): FinalFactAp? =
        access.filter(filter)?.let { AccessGraphFinalFactAp(base, it, exclusions) }

    override fun contains(factAp: InitialFactAp): Boolean {
        factAp as AccessGraphInitialFactAp

        if (base != factAp.base) return false
        return access.containsAllAccessPaths(factAp.access)
    }

    override fun equalTo(factAp: InitialFactAp): Boolean {
        factAp as AccessGraphInitialFactAp

        if (base != factAp.base) return false
        return access == factAp.access
    }
}
