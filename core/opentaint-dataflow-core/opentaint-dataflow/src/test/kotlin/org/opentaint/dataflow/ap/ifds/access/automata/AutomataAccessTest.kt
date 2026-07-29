package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.access.AnyFieldMarkExclusions
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertSame

class AutomataAccessTest {
    private val graphGenerator = RandomGraphGenerator()
    private val empty = graphGenerator.manager.emptyGraph()

    @Test
    fun `merging alternatives treats shape and AnyField mark exclusions as one value`() {
        val cleaned = empty.prepend(1)
            .withAnyFieldMarkExclusions(AnyFieldMarkExclusions.Empty.add(7))
        val uncleaned = empty.prepend(2)

        val merged = cleaned.merge(uncleaned)

        assertEquals(AnyFieldMarkExclusions.Empty, merged.anyFieldMarkExclusions)
        assertEquals(true, merged.containsAll(cleaned))
        assertEquals(true, merged.containsAll(uncleaned))
    }

    @Test
    fun `merging a contained value is identity`() {
        val access = empty.prepend(1)

        assertSame(access, access.merge(access))
    }
}
