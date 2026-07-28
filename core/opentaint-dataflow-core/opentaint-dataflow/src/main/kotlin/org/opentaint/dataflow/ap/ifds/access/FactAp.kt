package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor

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

    val size: Int
    val depth: Int
}

interface InitialFactAp : FactAp, ReadableAccessorList<InitialFactAp> {
    fun rebase(newBase: AccessPathBase): InitialFactAp
    fun exclude(accessor: Accessor): InitialFactAp
    fun replaceExclusions(exclusions: ExclusionSet): InitialFactAp

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

    fun prependAccessor(accessor: Accessor): FinalFactAp
    fun clearAccessor(accessor: Accessor): FinalFactAp?
    fun removeAbstraction(): FinalFactAp?
    fun abstractOnly(): FinalFactAp

    /**
     * The dual of [removeAbstraction]: the fact reduced to its root abstraction — no concrete
     * children, but everything the abstraction itself carries kept, in particular a starred
     * sanitizer's excluded-mark annotation (tree mode). Callers partitioning an abstract fact
     * must use this rather than rebuilding via `createAbstractAp`, which starts from a bare
     * abstract node and silently drops the claim. Only meaningful when [isAbstract] is true.
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
     * A starred sanitizer's whole-subtree clean, expressed structurally: every concrete `![mark]`
     * node strictly below at least one accessor is deleted (the mark carried by the base directly
     * is the rule's base clean action's job), and every abstract node is annotated with the
     * residual claim that the mark stays excluded from whatever materializes below it later.
     *
     * Representations that do not support the structural form return [DeepCleanResult.Unsupported]
     * and keep the legacy flat [org.opentaint.dataflow.ap.ifds.DeepMarkExclusion] channel.
     */
    fun deepClean(mark: TaintMarkAccessor): DeepCleanResult = DeepCleanResult.Unsupported

    sealed interface DeepCleanResult {
        /** This representation has no structural deep clean; use the legacy exclusion channel. */
        data object Unsupported : DeepCleanResult

        /** Nothing of the fact survived the clean. */
        data object RemovedCompletely : DeepCleanResult

        /** The fact after the clean; identical to the receiver when the clean found nothing. */
        data class Cleaned(val fact: FinalFactAp) : DeepCleanResult
    }
}
