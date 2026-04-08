package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.ReadableAccessorList
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import kotlin.collections.orEmpty

abstract class TreeSuffixBaseFact<T : Any>(
    val apManager: TreeSuffixApManager,
    override val base: AccessPathBase,
    val access: AccessPath.AccessNode?,
    val suffix: AccessTree.AccessNode,
    override val exclusions: ExclusionSet
) : FactAp, ReadableAccessorList<T> {
    val treeManager get() = apManager.treeManager

    override val size: Int
        get() = suffix.countNodes() + (access?.size ?: 0)

    abstract fun create(
        apManager: TreeSuffixApManager,
        base: AccessPathBase,
        access: AccessPath.AccessNode?,
        suffix: AccessTree.AccessNode,
        exclusions: ExclusionSet
    ): T

    fun rebase(newBase: AccessPathBase): T =
        create(apManager, newBase, access, suffix, exclusions)

    fun exclude(accessor: Accessor): T =
        create(apManager, base, access, suffix, exclusions.add(accessor))

    fun replaceExclusions(exclusions: ExclusionSet): T =
        create(apManager, base, access, suffix, exclusions)

    fun prependAccessor(accessor: Accessor): T = with(treeManager) {
        val newAccess = AccessPath.AccessNode(treeManager, accessor.idx, access)
        create(apManager, base, newAccess, suffix, exclusions)
    }

    fun clearAccessor(accessor: Accessor): T? = with(treeManager) {
        if (access != null) {
            if (access.accessor.accessor == accessor) return null
            @Suppress("UNCHECKED_CAST")
            return this@TreeSuffixBaseFact as T?
        }

        val newSuffix = suffix.clearChild(accessor.idx)
            .takeIf { !it.isEmpty }
            ?: return null

        create(apManager, base, access = null, newSuffix, exclusions)
    }

    override fun isAbstract(): Boolean =
        access == null && suffix.isAbstract

    override fun startsWithAccessor(accessor: Accessor): Boolean = with(treeManager) {
        if (access == null) {
            return suffix.contains(accessor.idx)
        }

        return access.accessor.accessor == accessor
    }

    override fun readAccessor(accessor: Accessor): T? = with(treeManager) {
        if (access != null) {
            if (access.accessor.accessor != accessor) return null
            return create(apManager, base, access.next, suffix, exclusions)
        }

        val newSuffix = suffix.getChild(accessor.idx)
            ?: return null

        create(apManager, base, access = null, newSuffix, exclusions)
    }

    override fun getStartAccessors(): Set<Accessor> = with(treeManager) {
        if (access != null) {
            return setOf(access.accessor.accessor)
        }

        return suffix.accessors?.mapTo(hashSetOf()) { it.accessor }.orEmpty()
    }

    override fun getAllAccessors(): Set<Accessor> = with(treeManager) {
        val accessorIds = IntOpenHashSet()
        if (access != null) {
            accessorIds += access.toList()
        }

        suffix.collectAccessorsTo(accessorIds)

        return accessorIds.mapTo(hashSetOf()) { it.accessor }
    }

    override fun toString(): String = buildString {
        val prefix = "$base${access ?: ""}"
        suffix.print(this, prefix, suffix = "/$exclusions")
        if (this[lastIndex] == '\n') {
            this.deleteCharAt(lastIndex)
        }
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as TreeSuffixBaseFact<*>

        if (base != other.base) return false
        if (access != other.access) return false
        if (suffix != other.suffix) return false
        if (exclusions != other.exclusions) return false

        return true
    }

    override fun hashCode(): Int {
        var result = base.hashCode()
        result = 31 * result + (access?.hashCode() ?: 0)
        result = 31 * result + suffix.hashCode()
        result = 31 * result + exclusions.hashCode()
        return result
    }
}

class TreeSuffixInitialFact(
    apManager: TreeSuffixApManager,
    base: AccessPathBase,
    access: AccessPath.AccessNode?,
    suffix: AccessTree.AccessNode,
    exclusions: ExclusionSet,
) : TreeSuffixBaseFact<InitialFactAp>(apManager, base, access, suffix, exclusions), InitialFactAp {
    override fun create(
        apManager: TreeSuffixApManager,
        base: AccessPathBase,
        access: AccessPath.AccessNode?,
        suffix: AccessTree.AccessNode,
        exclusions: ExclusionSet
    ): InitialFactAp = TreeSuffixInitialFact(apManager, base, access, suffix, exclusions)

    override fun splitDelta(other: FinalFactAp): List<Pair<InitialFactAp, InitialFactAp.Delta>> {
        TODO("Not yet implemented")
    }

    override fun concat(delta: InitialFactAp.Delta): InitialFactAp {
        TODO("Not yet implemented")
    }

    override fun contains(factAp: InitialFactAp): Boolean {
        TODO("Not yet implemented")
    }

    override fun compatibilityFilter(typeChecker: FactTypeChecker): FactTypeChecker.FactCompatibilityFilter {
//        TODO("Not yet implemented")
        return FactTypeChecker.AlwaysCompatibleFilter
    }
}

class TreeSuffixFinalFact(
    apManager: TreeSuffixApManager,
    base: AccessPathBase,
    access: AccessPath.AccessNode?,
    suffix: AccessTree.AccessNode,
    exclusions: ExclusionSet,
) : TreeSuffixBaseFact<FinalFactAp>(apManager, base, access, suffix, exclusions), FinalFactAp {
    override fun create(
        apManager: TreeSuffixApManager,
        base: AccessPathBase,
        access: AccessPath.AccessNode?,
        suffix: AccessTree.AccessNode,
        exclusions: ExclusionSet
    ): FinalFactAp = TreeSuffixFinalFact(apManager, base, access, suffix, exclusions)

    override fun removeAbstraction(): FinalFactAp? {
        TODO("Not yet implemented")
    }

    override fun delta(other: InitialFactAp): List<FinalFactAp.Delta> {
        TODO("Not yet implemented")
    }

    override fun concat(
        typeChecker: FactTypeChecker,
        delta: FinalFactAp.Delta
    ): FinalFactAp? {
        TODO("Not yet implemented")
    }

    override fun filterFact(filter: FactTypeChecker.FactApFilter): FinalFactAp {
//        TODO("Not yet implemented")
        return this
    }

    override fun filterFact(filter: FactTypeChecker.FactCompatibilityFilter): FinalFactAp {
//        TODO("Not yet implemented")
        return this
    }

    override fun contains(factAp: InitialFactAp): Boolean {
        TODO("Not yet implemented")
    }

    override fun equalTo(factAp: InitialFactAp): Boolean {
        TODO("Not yet implemented")
    }
}
