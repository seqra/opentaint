package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.VALUE_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTaintMarkAccessor

class BaseOnlyFinalFactAp(
    val manager: BaseOnlyApManager,
    override val base: AccessPathBase,
    val access: BaseOnlyAccess,
    exclusions: ExclusionSet,
) : FinalFactAp {
    override val exclusions: ExclusionSet = manager.compactExclusions(exclusions)

    init {
        BaseOnlyAccessOps.requireCanonical(access, allowTransientCollapsed = true)
    }

    override val size: Int get() = access.size
    override val depth: Int get() = size

    override fun isAbstract(): Boolean = access.isRootAbstract

    override fun rebase(newBase: AccessPathBase): FinalFactAp =
        BaseOnlyFinalFactAp(manager, newBase, BaseOnlyAccessOps.restoreAbstraction(access), exclusions)

    override fun exclude(accessor: Accessor): FinalFactAp =
        BaseOnlyFinalFactAp(manager, base, access, exclusions.add(accessor))

    override fun replaceExclusions(exclusions: ExclusionSet): FinalFactAp =
        BaseOnlyFinalFactAp(manager, base, access, exclusions)

    private fun rewrap(newAccess: BaseOnlyAccess): BaseOnlyFinalFactAp =
        BaseOnlyFinalFactAp(manager, base, newAccess, exclusions)

    override fun startsWithAccessor(accessor: Accessor): Boolean = manager.startsWithAccessor(access, accessor)

    override fun getStartAccessors(): Set<Accessor> = manager.startAccessors(access)

    override fun getAllAccessors(): Set<Accessor> = manager.allAccessors(access)

    override fun readAccessor(accessor: Accessor): FinalFactAp? = manager.readAccess(access, accessor)?.let(::rewrap)

    override fun prependAccessor(accessor: Accessor): FinalFactAp =
        rewrap(BaseOnlyAccessOps.prepend(access, manager.interner.index(accessor), manager.fieldSensitive))

    override fun clearAccessor(accessor: Accessor): FinalFactAp? =
        BaseOnlyAccessOps.clear(access, manager.interner.index(accessor))?.let(::rewrap)

    override fun clearAllAccessorOccurrences(accessor: Accessor, keepStartAccessor: Boolean): FinalFactAp? {
        if (accessor !is TaintMarkAccessor) {
            TODO("BaseOnly deep exclusion is defined for taint mark accessors only, got: $accessor")
        }
        val cleared = BaseOnlyAccessOps.clearAllOccurrences(
            access,
            manager.interner.index(accessor),
            keepStartAccessor,
        ) ?: return null
        return if (cleared == access) this else rewrap(cleared)
    }

    override fun removeAbstraction(): FinalFactAp? =
        BaseOnlyAccessOps.collapse(access).takeIf { !it.isEmpty }?.let(::rewrap)

    override fun abstractOnly(): FinalFactAp {
        val abstractAccess = access.withBaseOnlyAccessUnpacked { staticIdx, fieldIdx, _ ->
            when {
                staticIdx == ABSTRACT_MARK -> packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR)
                fieldIdx == ABSTRACT_MARK -> packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)
                else -> ABSTRACT_EMPTY_ACCESS
            }
        }
        return rewrap(abstractAccess)
    }

    override fun filterFact(filter: FactTypeChecker.FactApFilter): FinalFactAp? =
        filterAccess(filter)?.let { filtered -> if (filtered == access) this else rewrap(filtered) }

    override fun filterFact(filter: FactTypeChecker.FactCompatibilityFilter): FinalFactAp? {
        if (filter is FactTypeChecker.AlwaysCompatibleFilter) return this
        if (!access.hasAp) return this

        val predecessor = when (access.apSlot) {
            0 -> NO_ACCESSOR
            1 -> access.staticIdx
            2 -> if (access.fieldIdx >= 0) access.fieldIdx else access.staticIdx
            else -> error("Canonical abstract fact has no abstraction slot: $access")
        }
        if (predecessor < 0) return this
        val accessor = manager.interner.accessor(predecessor)
            ?: error("Accessor not found: $predecessor")
        return when (filter.check(accessor)) {
            FactTypeChecker.CompatibilityFilterResult.Compatible -> this
            FactTypeChecker.CompatibilityFilterResult.NotCompatible -> null
        }
    }

    private fun filterAccess(
        filter: FactTypeChecker.FactApFilter,
        candidate: BaseOnlyAccess = access,
    ): BaseOnlyAccess? {
        if (!candidate.hasSemanticMark) {
            return candidate.takeIf { logicalPaths(candidate).any { path -> pathAccepted(filter, path) } }
        }
        val common = logicalPrefix(candidate)
        val path = when (candidate.valueAccessorState) {
            BaseOnlyValueAccessorState.Normal -> common + intArrayOf(candidate.suffixIdx, FINAL_ACCESSOR_IDX)
            BaseOnlyValueAccessorState.Value -> {
                val valueAccessor =
                    if (candidate.hasTypeInfoSuffix) TYPE_INFO_GROUP_ACCESSOR_IDX else VALUE_ACCESSOR_IDX
                common + intArrayOf(valueAccessor, candidate.suffixIdx, FINAL_ACCESSOR_IDX)
            }
        }
        return candidate.takeIf { pathAccepted(filter, path) }
    }

    private fun pathAccepted(filter: FactTypeChecker.FactApFilter, path: IntArray): Boolean {
        var current = filter
        path.forEach { idx ->
            val accessor = manager.interner.accessor(idx) ?: error("Accessor not found: $idx")
            when (val result = current.check(accessor)) {
                FactTypeChecker.FilterResult.Accept -> return true
                FactTypeChecker.FilterResult.Reject -> return false
                is FactTypeChecker.FilterResult.FilterNext -> current = result.filter
            }
        }
        return true
    }


    private fun logicalPaths(candidate: BaseOnlyAccess): List<IntArray> {
        val common = logicalPrefix(candidate)
        val suffix = candidate.suffixIdx
        if (suffix < 0) return listOf(common)
        if (suffix == FINAL_ACCESSOR_IDX) return listOf(common + FINAL_ACCESSOR_IDX)
        if (candidate.hasTypeInfoSuffix) {
            return listOf(terminalLogicalPath(candidate, common, TYPE_INFO_GROUP_ACCESSOR_IDX))
        }
        if (suffix.isTaintMarkAccessor()) {
            return listOf(terminalLogicalPath(candidate, common, VALUE_ACCESSOR_IDX))
        }
        return listOf(common + intArrayOf(suffix, FINAL_ACCESSOR_IDX))
    }

    private fun logicalPrefix(candidate: BaseOnlyAccess): IntArray = buildList {
        if (candidate.staticIdx >= 0) add(candidate.staticIdx)
        if (candidate.fieldIdx >= 0) add(candidate.fieldIdx)
    }.toIntArray()

    private fun terminalLogicalPath(
        candidate: BaseOnlyAccess,
        common: IntArray,
        valueAccessor: Int,
    ): IntArray = when (candidate.valueAccessorState) {
        BaseOnlyValueAccessorState.Normal -> common + intArrayOf(candidate.suffixIdx, FINAL_ACCESSOR_IDX)
        BaseOnlyValueAccessorState.Value ->
            common + intArrayOf(valueAccessor, candidate.suffixIdx, FINAL_ACCESSOR_IDX)
    }

    override fun contains(factAp: InitialFactAp): Boolean {
        factAp as BaseOnlyInitialFactAp
        if (base != factAp.base) return false
        if (!BaseOnlyAccessOps.containsAccess(access, factAp.access)) return false
        val residualHead = BaseOnlyAccessOps.firstAccessorAfterAbstraction(access, factAp.access)
            ?: return true
        val accessor = manager.interner.accessor(residualHead) ?: return true
        return accessor !in exclusions
    }

    override fun equalTo(factAp: InitialFactAp): Boolean {
        factAp as BaseOnlyInitialFactAp
        if (base != factAp.base) return false
        return BaseOnlyAccessOps.equalToInitial(access, factAp.access)
    }

    override fun delta(other: InitialFactAp): List<FinalFactAp.Delta> {
        other as BaseOnlyInitialFactAp
        if (base != other.base) return emptyList()
        val match = BaseOnlyAccessOps.matchPrefix(access, other.access)
        val result = ArrayList<FinalFactAp.Delta>(2)
        if (match.emptyDelta) result.add(BaseOnlyEmptyFinalDelta)
        if (match.hasSuffix) {
            manager.applyExclusions(match.suffix, other.exclusions)?.let { suffix ->
                result.add(BaseOnlyNodeFinalDelta(manager, suffix))
            }
        }
        return result
    }

    override fun hasEmptyDelta(other: InitialFactAp): Boolean {
        other as BaseOnlyInitialFactAp
        return base == other.base && access == other.access
    }

    override fun concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp? {
        return when (val d = delta as BaseOnlyFinalDelta) {
            BaseOnlyEmptyFinalDelta -> this
            is BaseOnlyNodeFinalDelta -> {
                val filteredDelta = filterDelta(typeChecker, d.access) ?: return null
                BaseOnlyAccessOps.appendFinal(access, filteredDelta)?.let(::rewrap)
            }
        }
    }

    private fun filterDelta(typeChecker: FactTypeChecker, delta: BaseOnlyAccess): BaseOnlyAccess? {
        val prefix = buildList {
            access.forEachCoreIdx { idx ->
                add(manager.interner.accessor(idx) ?: error("Accessor not found: $idx"))
            }
        }
        return filterAccess(typeChecker.accessPathFilter(prefix), delta)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is BaseOnlyFinalFactAp) return false
        return base == other.base && access == other.access && exclusions == other.exclusions
    }

    override fun hashCode(): Int {
        var result = base.hashCode()
        result = 31 * result + access.hashCode()
        result = 31 * result + exclusions.hashCode()
        return result
    }

    override fun toString(): String = "$base${manager.renderAccess(access)}/$exclusions"
}
