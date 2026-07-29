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
        val cleaned = AutomataFinalAccess(empty.prepend(1), AnyFieldMarkExclusions.Empty.add(7))
        val uncleaned = AutomataFinalAccess(empty.prepend(2), AnyFieldMarkExclusions.Empty)

        val merged = cleaned.mergeAdd(uncleaned)

        assertEquals(AnyFieldMarkExclusions.Empty, merged.anyFieldMarkExclusions)
        assertEquals(true, merged.access.containsAll(cleaned.access))
        assertEquals(true, merged.access.containsAll(uncleaned.access))
    }

    @Test
    fun `merging a contained value is identity`() {
        val access = AutomataFinalAccess(empty.prepend(1), AnyFieldMarkExclusions.Empty)

        assertSame(access, access.mergeAdd(access))
    }
}
