package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.taint.Cleaner

interface AccessorList {
    fun startsWithAccessor(accessor: Accessor): Boolean
    fun getStartAccessors(): Set<Accessor>
    fun getAllAccessors(): Set<Accessor>

    fun isAbstract(): Boolean
}

interface ReadableAccessorList<T : Any> : AccessorList {
    fun readAccessor(accessor: Accessor): T?
}

interface FactAp: AccessorList {
    val base: AccessPathBase
    val exclusions: ExclusionSet
    val demandState: FactDemandState get() = FactDemandState(exclusions)

    val size: Int
    val depth: Int
}

interface InitialFactAp : FactAp, ReadableAccessorList<InitialFactAp> {
    fun rebase(newBase: AccessPathBase): InitialFactAp
    fun exclude(accessor: Accessor): InitialFactAp
    fun replaceExclusions(exclusions: ExclusionSet): InitialFactAp
    fun replaceDemandState(demandState: FactDemandState): InitialFactAp =
        replaceExclusions(demandState.exclusions)

    fun prependAccessor(accessor: Accessor): InitialFactAp
    fun clearAccessor(accessor: Accessor): InitialFactAp?

    interface Delta: ReadableAccessorList<Delta> {
        val isEmpty: Boolean

        fun concat(other: Delta): Delta
    }

    fun splitDelta(other: FinalFactAp): List<Pair<InitialFactAp, Delta>>
    fun concat(delta: Delta): InitialFactAp

    fun contains(factAp: InitialFactAp): Boolean

    fun compatibilityFilter(typeChecker: FactTypeChecker): FactTypeChecker.FactCompatibilityFilter
}

interface FinalFactAp : FactAp, ReadableAccessorList<FinalFactAp> {
    fun rebase(newBase: AccessPathBase): FinalFactAp
    fun exclude(accessor: Accessor): FinalFactAp
    fun replaceExclusions(exclusions: ExclusionSet): FinalFactAp
    fun replaceDemandState(demandState: FactDemandState): FinalFactAp =
        replaceExclusions(demandState.exclusions)

    fun prependAccessor(accessor: Accessor): FinalFactAp
    fun clearAccessor(accessor: Accessor): FinalFactAp?
    fun removeAbstraction(): FinalFactAp?
    fun abstractOnly(): FinalFactAp

    /**
     * The dual of [removeAbstraction]: the fact reduced to its root abstraction — no concrete
     * children, but all representation state attached to the abstraction preserved. Callers
     * partitioning an abstract fact must use this rather than rebuilding a bare abstraction.
     * Only meaningful when [isAbstract] is true.
     */
    fun abstractPart(): FinalFactAp

    interface Delta: ReadableAccessorList<Delta> {
        val isEmpty: Boolean
    }

    fun delta(other: InitialFactAp): List<Delta>
    fun concat(typeChecker: FactTypeChecker, delta: Delta): FinalFactAp?

    fun filterFact(filter: FactTypeChecker.FactApFilter): FinalFactAp?
    fun filterFact(filter: FactTypeChecker.FactCompatibilityFilter): FinalFactAp?

    fun contains(factAp: InitialFactAp): Boolean
    fun equalTo(factAp: InitialFactAp): Boolean

    fun hasEmptyDelta(other: InitialFactAp): Boolean =
        delta(other).any { it.isEmpty }

    /**
     * Applies one cleaner position to this fact.
     *
     * A concrete position is removed directly. If the position crosses an abstract any-field,
     * the representation also retains whatever residual effect is needed to clean content that
     * materializes later. Callers do not distinguish those cases.
     */
    fun clean(cleaner: Cleaner): CleanResult

    /**
     * Removes a mark from both the exact position and its currently represented any-field
     * alternative, without creating a persistent any-field cleaner effect.
     */
    fun cleanExactAndAnyField(mark: TaintMarkAccessor): CleanResult {
        val afterAny = readAccessor(AnyAccessor)
            ?: error("Fact reports an any-field accessor but cannot read it")

        val clearedAfterAny = afterAny.clearAccessor(mark)
        val restoredAfterAny = clearedAfterAny?.prependAccessor(AnyAccessor)

        val withoutAny = clearAccessor(AnyAccessor)
        val cleanedWithoutAny = withoutAny?.clearAccessor(mark)

        val cleaned = clearedAfterAny != afterAny || cleanedWithoutAny != withoutAny
        return CleanResult(
            listOfNotNull(restoredAfterAny, cleanedWithoutAny),
            removedAlternative = cleaned,
        )
    }

    data class CleanResult(
        val survivingFacts: List<FinalFactAp>,
        val removedAlternative: Boolean,
    )
}
