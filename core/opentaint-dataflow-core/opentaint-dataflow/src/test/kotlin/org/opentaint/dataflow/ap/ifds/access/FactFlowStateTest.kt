package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertSame
import kotlin.test.assertTrue

class FactFlowStateTest {
    private val fieldA = FieldAccessor("Owner", "a", "java.lang.String")
    private val fieldB = FieldAccessor("Owner", "b", "java.lang.String")
    private val markA = TaintMarkAccessor("a")
    private val markB = TaintMarkAccessor("b")

    @Test
    fun `then composes analysis refinements and cleaner effects`() {
        val before = FactFlowState(ExclusionSet.Concrete(fieldA)).cleanDeep(markA)
        val after = FactFlowState(ExclusionSet.Concrete(fieldB)).cleanDeep(markB)

        val result = before then after

        assertTrue(fieldA in result.exclusions)
        assertTrue(fieldB in result.exclusions)
        assertTrue(markA in result.deepCleanEffects)
        assertTrue(markB in result.deepCleanEffects)
    }

    @Test
    fun `join keeps only cleaner effects shared by every alternative`() {
        val cleaned = FactFlowState(ExclusionSet.Concrete(fieldA))
            .cleanDeep(markA)
            .cleanDeep(markB)
        val alternative = FactFlowState(ExclusionSet.Concrete(fieldB))
            .cleanDeep(markA)

        val result = cleaned join alternative

        assertTrue(fieldA in result.exclusions)
        assertTrue(fieldB in result.exclusions)
        assertTrue(markA in result.deepCleanEffects)
        assertFalse(markB in result.deepCleanEffects)
    }

    @Test
    fun `analysis exclusions combine without cleaner semantics`() {
        val exclusions = ExclusionSet.Concrete(fieldA).union(ExclusionSet.Concrete(fieldB))

        assertTrue(fieldA in exclusions)
        assertTrue(fieldB in exclusions)
    }

    @Test
    fun `unchanged composition and join preserve identity`() {
        val state = FactFlowState(ExclusionSet.Concrete(fieldA)).cleanDeep(markA)

        assertSame(state, state then FactFlowState.Empty)
        assertSame(state, state join state)
    }

    @Test
    fun `universe cannot acquire deferred cleaner effects`() {
        assertSame(FactFlowState.Universe, FactFlowState.Universe.cleanDeep(markA))

        val cleaned = FactFlowState.Empty.cleanDeep(markA)
        assertSame(FactFlowState.Universe, cleaned.withExclusions(ExclusionSet.Universe))
    }
}
