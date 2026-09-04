package org.opentaint.dataflow.ap.ifds

import kotlinx.collections.immutable.persistentHashSetOf
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull

class ExclusionSetTest {
    private val first = TaintMarkAccessor("first")
    private val second = TaintMarkAccessor("second")
    private val third = TaintMarkAccessor("third")

    @Test
    fun `single-accessor changes keep an eagerly computed hash`() {
        val singleton = ExclusionSet.Concrete(first)
        assertNotNull(singleton.cachedHash())

        val added = singleton.add(second) as ExclusionSet.Concrete
        assertNotNull(added.cachedHash())

        val subtracted = added.subtract(first) as ExclusionSet.Concrete
        assertNotNull(subtracted.cachedHash())
    }

    @Test
    fun `bulk operations defer full hash computation`() {
        val left = ExclusionSet.Concrete(first).add(second) as ExclusionSet.Concrete
        val right = ExclusionSet.Concrete(second).add(third) as ExclusionSet.Concrete

        val union = left.union(right) as ExclusionSet.Concrete
        assertNull(union.cachedHash())
        assertEquals(union.set.hashCode(), union.hashCode())
        assertNotNull(union.cachedHash())

        val intersection = left.intersect(right) as ExclusionSet.Concrete
        assertNull(intersection.cachedHash())
        assertEquals(intersection.set.hashCode(), intersection.hashCode())
        assertNotNull(intersection.cachedHash())
    }

    @Test
    fun `equality does not force a deferred hash`() {
        val left = ExclusionSet.Concrete(persistentHashSetOf(first, second))
        val right = ExclusionSet.Concrete(persistentHashSetOf(first, second))

        assertEquals(left, right)
        assertNull(left.cachedHash())
        assertNull(right.cachedHash())
    }

    private fun ExclusionSet.Concrete.cachedHash(): Int? = cachedHashField.get(this) as Int?

    private companion object {
        val cachedHashField = ExclusionSet.Concrete::class.java.getDeclaredField("cachedHash").apply {
            isAccessible = true
        }
    }
}
