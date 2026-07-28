package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import kotlin.test.Test
import kotlin.test.assertSame
import kotlin.test.assertTrue

class FactDemandStateTest {
    private val fieldA = FieldAccessor("Owner", "a", "java.lang.String")
    private val fieldB = FieldAccessor("Owner", "b", "java.lang.String")
    @Test
    fun `then composes demand-analysis exclusions`() {
        val before = FactDemandState(ExclusionSet.Concrete(fieldA))
        val after = FactDemandState(ExclusionSet.Concrete(fieldB))

        val result = before then after

        assertTrue(fieldA in result.exclusions)
        assertTrue(fieldB in result.exclusions)
    }

    @Test
    fun `join composes demand-analysis exclusions`() {
        val first = FactDemandState(ExclusionSet.Concrete(fieldA))
        val alternative = FactDemandState(ExclusionSet.Concrete(fieldB))

        val result = first join alternative

        assertTrue(fieldA in result.exclusions)
        assertTrue(fieldB in result.exclusions)
    }

    @Test
    fun `analysis exclusions combine without cleaner semantics`() {
        val exclusions = ExclusionSet.Concrete(fieldA).union(ExclusionSet.Concrete(fieldB))

        assertTrue(fieldA in exclusions)
        assertTrue(fieldB in exclusions)
    }

    @Test
    fun `unchanged composition and join preserve identity`() {
        val state = FactDemandState(ExclusionSet.Concrete(fieldA))

        assertSame(state, state then FactDemandState.Empty)
        assertSame(state, state join state)
    }
}
