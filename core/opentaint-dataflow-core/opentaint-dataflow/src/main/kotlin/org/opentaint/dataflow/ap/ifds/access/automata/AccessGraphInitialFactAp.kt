package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.forExclusions

data class AccessGraphInitialFactAp(
    override val base: AccessPathBase,
    override val access: AccessGraph,
    override val exclusions: ExclusionSet,
    val anyFieldCleanerEffects: AnyFieldCleanerEffects = AnyFieldCleanerEffects.Empty,
) : InitialFactAp, AccessGraphAccessorList {
    init {
        check(exclusions !is ExclusionSet.Universe || anyFieldCleanerEffects.isEmpty) {
            "Universe facts cannot carry cleaner effects"
        }
    }

    override val size: Int get() = access.size
    override val depth: Int get() = size

    override fun rebase(newBase: AccessPathBase): InitialFactAp =
        AccessGraphInitialFactAp(newBase, access, exclusions, anyFieldCleanerEffects)

    override fun isAbstract(): Boolean =
        exclusions !is ExclusionSet.Universe && access.initialNodeIsFinal()

    override fun exclude(accessor: Accessor): InitialFactAp {
        check(accessor !is AnyAccessor)
        return AccessGraphInitialFactAp(base, access, exclusions.add(accessor), anyFieldCleanerEffects)
    }

    override fun replaceExclusions(exclusions: ExclusionSet): InitialFactAp =
        AccessGraphInitialFactAp(
            base,
            access,
            exclusions,
            anyFieldCleanerEffects.takeUnless { exclusions is ExclusionSet.Universe }
                ?: AnyFieldCleanerEffects.Empty,
        )

    override fun readAccessor(accessor: Accessor): InitialFactAp? = with(access.manager) {
        check(accessor !is AnyAccessor)
        return access.read(accessor.idx)?.let {
            AccessGraphInitialFactAp(base, it, exclusions, anyFieldCleanerEffects)
        }
    }

    override fun prependAccessor(accessor: Accessor): InitialFactAp = with(access.manager) {
        check(accessor !is AnyAccessor)
        return AccessGraphInitialFactAp(base, access.prepend(accessor.idx), exclusions, anyFieldCleanerEffects)
    }

    override fun clearAccessor(accessor: Accessor): InitialFactAp? = with(access.manager) {
        check(accessor !is AnyAccessor)
        return access.clear(accessor.idx)?.let {
            AccessGraphInitialFactAp(base, it, exclusions, anyFieldCleanerEffects)
        }
    }

    data class Delta(
        override val access: AccessGraph,
        val anyFieldCleanerEffects: AnyFieldCleanerEffects,
    ) : InitialFactAp.Delta, AccessGraphAccessorList {
        override val isEmpty: Boolean get() = access.isEmpty()

        override fun concat(other: InitialFactAp.Delta): InitialFactAp.Delta {
            other as Delta

            return Delta(access.concat(other.access), anyFieldCleanerEffects then other.anyFieldCleanerEffects)
        }

        override fun readAccessor(accessor: Accessor): InitialFactAp.Delta? = with(access.manager) {
            val newGraph = access.read(accessor.idx) ?: return@with null
            return Delta(newGraph, anyFieldCleanerEffects)
        }

        override fun isAbstract(): Boolean = access.initialNodeIsFinal()
    }

    override fun splitDelta(other: FinalFactAp): List<Pair<InitialFactAp, InitialFactAp.Delta>> {
        other as AccessGraphFinalFactAp
        if (base != other.base) return emptyList()

        if (other.access.isEmpty()) {
            val filteredDelta = this.access
                .filter(other.exclusions)
                ?.enforceAnyFieldCleaners(other.anyFieldCleanerEffects, keepInitialLevel = true)
                ?: return emptyList()

            val emptyFact = AccessGraphInitialFactAp(
                base, access.manager.emptyGraph(), exclusions, anyFieldCleanerEffects
            )
            return listOf(emptyFact to Delta(filteredDelta, anyFieldCleanerEffects))
        }

        return access.splitDelta(other.access).mapNotNull { (matchedAccess, delta) ->
            val filteredDelta = delta
                .filter(other.exclusions)
                ?.enforceAnyFieldCleaners(other.anyFieldCleanerEffects, keepInitialLevel = matchedAccess.isEmpty())
                ?: return@mapNotNull null

            val matchedFact = AccessGraphInitialFactAp(base, matchedAccess, exclusions, anyFieldCleanerEffects)
            matchedFact to Delta(filteredDelta, anyFieldCleanerEffects)
        }
    }

    override fun concat(delta: InitialFactAp.Delta): InitialFactAp {
        delta as Delta
        val composedEffects = (anyFieldCleanerEffects then delta.anyFieldCleanerEffects)
            .forExclusions(exclusions)
        if (delta.isEmpty) {
            return AccessGraphInitialFactAp(base, access, exclusions, composedEffects)
        }

        val concatenatedGraph = access.concat(delta.access)
        return AccessGraphInitialFactAp(
            base, concatenatedGraph, exclusions, composedEffects
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
