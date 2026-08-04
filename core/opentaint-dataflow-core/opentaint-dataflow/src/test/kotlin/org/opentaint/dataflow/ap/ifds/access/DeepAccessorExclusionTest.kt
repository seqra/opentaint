package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.access.DeepAccessorExclusion.Companion.addAccessorFromDepth0
import kotlin.test.Test
import kotlin.test.assertContentEquals
import kotlin.test.assertEquals

class DeepAccessorExclusionTest {
    @Test
    fun `base clean starts at depth one and collapses below an accessor`() {
        val atBase = null.add(7)
        assertContentEquals(intArrayOf(7), atBase.accessorsFromDepth1)

        val belowBase = atBase.collapseToDepth0()
        assertContentEquals(intArrayOf(7), belowBase.accessorsFromDepth0)
        assertContentEquals(intArrayOf(), belowBase.accessorsFromDepth1)
    }

    @Test
    fun `sequential composition keeps all claims at their strongest depth`() {
        val depth0 = null.addAccessorFromDepth0(1)
        val depth1 = null.add(1).add(2)

        val composed = DeepAccessorExclusion.merge(depth0, depth1)

        assertContentEquals(intArrayOf(1), composed?.accessorsFromDepth0)
        assertContentEquals(intArrayOf(2), composed?.accessorsFromDepth1)
    }

    @Test
    fun `alternative join keeps shared claims at their weakest depth`() {
        val stronger = null
            .addAccessorFromDepth0(1)
            .addAccessorFromDepth0(2)
        val weaker = null.add(1).add(3)

        val joined = DeepAccessorExclusion.intersect(stronger, weaker)

        assertContentEquals(intArrayOf(), joined?.accessorsFromDepth0)
        assertContentEquals(intArrayOf(1), joined?.accessorsFromDepth1)
        assertEquals(joined, DeepAccessorExclusion.intersect(weaker, stronger))
    }
}
