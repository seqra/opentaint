package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.access.AnyFieldMarkExclusions.Companion.addMarkFromDepth1
import kotlin.test.Test
import kotlin.test.assertContentEquals
import kotlin.test.assertEquals

class AnyFieldMarkExclusionsTest {
    @Test
    fun `base clean starts at depth two and collapses below an accessor`() {
        val atBase = AnyFieldMarkExclusions.Empty.add(7)
        assertContentEquals(intArrayOf(7), atBase.marksFromDepth2)

        val belowBase = atBase.collapseToDepth1()
        assertContentEquals(intArrayOf(7), belowBase.marksFromDepth1)
        assertContentEquals(intArrayOf(), belowBase.marksFromDepth2)
    }

    @Test
    fun `sequential composition keeps all claims at their strongest depth`() {
        val depth1 = AnyFieldMarkExclusions.Empty.addMarkFromDepth1(1)
        val depth2 = AnyFieldMarkExclusions.Empty.add(1).add(2)

        val composed = depth1 then depth2

        assertContentEquals(intArrayOf(1), composed.marksFromDepth1)
        assertContentEquals(intArrayOf(2), composed.marksFromDepth2)
    }

    @Test
    fun `alternative join keeps shared claims at their weakest depth`() {
        val stronger = AnyFieldMarkExclusions.Empty
            .addMarkFromDepth1(1)
            .addMarkFromDepth1(2)
        val weaker = AnyFieldMarkExclusions.Empty.add(1).add(3)

        val joined = stronger join weaker

        assertContentEquals(intArrayOf(), joined.marksFromDepth1)
        assertContentEquals(intArrayOf(1), joined.marksFromDepth2)
        assertEquals(joined, weaker join stronger)
    }
}
