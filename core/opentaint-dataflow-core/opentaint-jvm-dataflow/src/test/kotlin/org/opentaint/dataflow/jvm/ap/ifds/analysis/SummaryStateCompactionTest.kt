package org.opentaint.dataflow.jvm.ap.ifds.analysis

import kotlin.test.Test
import kotlin.test.assertEquals

class SummaryStateCompactionTest {
    @Test
    fun `removed and equal summary states are compacted`() {
        val states = linkedMapOf<Int, String>()

        states.retainCanonicalSummaryState(null) { it.length }
        states.retainCanonicalSummaryState("first") { it.length }
        states.retainCanonicalSummaryState("other") { it.length }
        states.retainCanonicalSummaryState("four") { it.length }

        assertEquals(listOf("first", "four"), states.values.toList())
    }
}
