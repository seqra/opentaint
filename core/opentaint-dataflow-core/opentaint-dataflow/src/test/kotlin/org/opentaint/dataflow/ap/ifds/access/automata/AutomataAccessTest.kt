package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.add
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertSame

class AutomataAccessTest {
    private val graphGenerator = RandomGraphGenerator()
    private val empty = graphGenerator.manager.emptyGraph()

    @Test
    fun `merging alternatives treats shape and AnyField mark exclusions as one value`() {
        val cleaned = empty.prepend(1)
            .withAnyFieldAccessorExclusions(null.add(7))
        val uncleaned = empty.prepend(2)

        val merged = cleaned.merge(uncleaned)

        assertEquals(null, merged.deepAccessorExclusion)
        assertEquals(true, merged.containsAll(cleaned))
        assertEquals(true, merged.containsAll(uncleaned))
    }

    @Test
    fun `merging a contained value is identity`() {
        val access = empty.prepend(1)

        assertSame(access, access.merge(access))
    }

    @Test
    fun `the abstract empty graph survives an always-compatible filter`() {
        assertSame(empty, empty.filter(FactTypeChecker.AlwaysCompatibleFilter))
    }

    @Test
    fun `the abstract empty graph has no trailing accessor for a compatibility filter to reject`() {
        val rejectAccessors = object : FactTypeChecker.FactCompatibilityFilter {
            override fun check(accessor: Accessor) =
                FactTypeChecker.CompatibilityFilterResult.NotCompatible
        }

        assertSame(empty, empty.filter(rejectAccessors))
    }
}
