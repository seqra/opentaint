package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertSame
import kotlin.test.assertTrue

class AnyFieldCleanerEffectsTest {
    private val markA = TaintMarkAccessor("a")
    private val markB = TaintMarkAccessor("b")

    @Test
    fun `then retains every cleaner performed in sequence`() {
        val before = AnyFieldCleanerEffects.Empty.add(markA)
        val after = AnyFieldCleanerEffects.Empty.add(markB)

        val result = before then after

        assertTrue(markA in result)
        assertTrue(markB in result)
    }

    @Test
    fun `join retains only cleaners performed by every alternative`() {
        val cleaned = AnyFieldCleanerEffects.Empty.add(markA).add(markB)
        val alternative = AnyFieldCleanerEffects.Empty.add(markA)

        val result = cleaned join alternative

        assertTrue(markA in result)
        assertFalse(markB in result)
    }

    @Test
    fun `operations reuse an operand when the semantic value is unchanged`() {
        val smaller = AnyFieldCleanerEffects.Empty.add(markA)
        val larger = smaller.add(markB)

        assertSame(larger, smaller then larger)
        assertSame(smaller, larger join smaller)
    }
}
