package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx

class DeepAccessorExclusion private constructor(
    @JvmField val accessorsFromDepth0: IntArray,
    @JvmField val accessorsFromDepth1: IntArray,
) {
    private val hash: Int = accessorsFromDepth0.contentHashCode() * 31 + accessorsFromDepth1.contentHashCode()

    override fun hashCode(): Int = hash

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is DeepAccessorExclusion) return false
        if (hash != other.hash) return false
        return accessorsFromDepth0.contentEquals(other.accessorsFromDepth0) &&
                accessorsFromDepth1.contentEquals(other.accessorsFromDepth1)
    }

    operator fun contains(accessor: AccessorIdx): Boolean =
        accessorsFromDepth0.binarySearch(accessor) >= 0 || accessorsFromDepth1.binarySearch(accessor) >= 0

    private fun allAccessors(): IntArray = (accessorsFromDepth0 + accessorsFromDepth1).also { it.sort() }

    fun collapseToDepth0(): DeepAccessorExclusion =
        if (accessorsFromDepth1.isEmpty()) this else DeepAccessorExclusion(allAccessors(), EMPTY)

    override fun toString(): String = buildString {
        append("!*{d0=")
        append(accessorsFromDepth0.joinToString(","))
        append(";d1=")
        append(accessorsFromDepth1.joinToString(","))
        append("}")
    }

    companion object {
        private val EMPTY = IntArray(0)

        fun create(accessorsFromDepth0: IntArray, accessorsFromDepth1: IntArray): DeepAccessorExclusion? {
            val depth1 = if (accessorsFromDepth1.any { accessorsFromDepth0.binarySearch(it) >= 0 }) {
                accessorsFromDepth1.filter { accessorsFromDepth0.binarySearch(it) < 0 }.toIntArray()
            } else {
                accessorsFromDepth1
            }

            if (accessorsFromDepth0.isEmpty() && depth1.isEmpty()) return null
            return DeepAccessorExclusion(accessorsFromDepth0, depth1)
        }

        private fun fromDepth0(accessor: AccessorIdx): DeepAccessorExclusion =
            DeepAccessorExclusion(intArrayOf(accessor), EMPTY)

        private fun fromDepth1(accessor: AccessorIdx): DeepAccessorExclusion =
            DeepAccessorExclusion(EMPTY, intArrayOf(accessor))

        fun DeepAccessorExclusion?.addAccessorFromDepth0(accessor: AccessorIdx): DeepAccessorExclusion {
            if (this == null) return fromDepth0(accessor)
            if (accessorsFromDepth0.binarySearch(accessor) >= 0) return this
            val depth0 = (accessorsFromDepth0 + accessor).also { it.sort() }
            val depth1 = accessorsFromDepth1.filter { it != accessor }.toIntArray()
            return DeepAccessorExclusion(depth0, depth1)
        }

        fun DeepAccessorExclusion?.addAccessorFromDepth1(accessor: AccessorIdx): DeepAccessorExclusion {
            if (this == null) return fromDepth1(accessor)
            if (accessor in this) return this
            val depth1 = (accessorsFromDepth1 + accessor).also { it.sort() }
            return DeepAccessorExclusion(accessorsFromDepth0, depth1)
        }

        fun intersect(a: DeepAccessorExclusion?, b: DeepAccessorExclusion?): DeepAccessorExclusion? {
            if (a == null || b == null) return null
            if (a == b) return a

            val depth0 = a.accessorsFromDepth0.filter {
                b.accessorsFromDepth0.binarySearch(it) >= 0
            }.toIntArray()
            val depth1 = mutableListOf<Int>()
            for (accessor in a.allAccessors()) {
                if (depth0.binarySearch(accessor) >= 0) continue
                if (accessor in b) depth1.add(accessor)
            }
            return create(depth0, depth1.toIntArray())
        }

        fun merge(a: DeepAccessorExclusion?, b: DeepAccessorExclusion?): DeepAccessorExclusion? {
            if (a == null) return b
            if (b == null) return a
            if (a == b) return a

            val depth0 = (a.accessorsFromDepth0.toSet() + b.accessorsFromDepth0.toSet())
                .toIntArray().also { it.sort() }
            val depth1 = (a.accessorsFromDepth1.toSet() + b.accessorsFromDepth1.toSet())
                .filter { depth0.binarySearch(it) < 0 }
                .toIntArray().also { it.sort() }
            return create(depth0, depth1)
        }
    }
}

fun DeepAccessorExclusion?.add(accessor: AccessorIdx): DeepAccessorExclusion =
    with(DeepAccessorExclusion) { addAccessorFromDepth1(accessor) }

fun DeepAccessorExclusion?.forExclusions(exclusions: ExclusionSet): DeepAccessorExclusion? =
    if (exclusions is ExclusionSet.Universe) null else this
