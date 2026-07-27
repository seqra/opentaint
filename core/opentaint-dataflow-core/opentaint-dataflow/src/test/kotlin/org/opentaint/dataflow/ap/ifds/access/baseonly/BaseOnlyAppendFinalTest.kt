package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

class BaseOnlyAppendFinalTest {
    private val accessors = AccessorInterner()
    private val ai = BaseOnlyAccessOps
    private val field = FieldAccessor("A", "f", "B")
    private val field2 = FieldAccessor("A", "g", "B")
    private val mark = TaintMarkAccessor("m")
    private val stat = ClassStaticAccessor("T")
    private fun i(a: org.opentaint.dataflow.ap.ifds.Accessor) = accessors.index(a)
    private fun chain(vararg a: org.opentaint.dataflow.ap.ifds.Accessor, abstract: Boolean = false): BaseOnlyAccess =
        ai.build(IntArray(a.size) { i(a[it]) }, abstract)

    // same-kind splices succeed (receiver hole slot == delta first-accessor slot)
    @Test fun `AP@static receiver accepts a static-leading delta`() {
        val recv = ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0)          // (-2,-1,-1)
        assertEquals(chain(stat, mark), ai.appendFinal(recv, chain(stat, mark)))
    }
    @Test fun `AP@suffix receiver accepts a terminal-leading delta`() {
        val recv = ai.abstractAt(NO_ACCESSOR, i(field), 2)            // (-1,f,-2)
        assertEquals(chain(field, mark), ai.appendFinal(recv, chain(mark)))
    }
    @Test fun `empty delta is identity`() {
        val recv = ai.abstractEmpty
        assertEquals(recv, ai.appendFinal(recv, ai.empty))
    }

    // A representational category mismatch is widened rather than rejected.
    @Test fun `AP@suffix receiver retains terminal after absorbing a field-leading semantic delta`() {
        val recv = ai.abstractAt(NO_ACCESSOR, i(field), 2)           // (-1,f,-2), hole at slot 2
        assertEquals(chain(field, mark), ai.appendFinal(recv, chain(field2, mark)))
    }
    @Test fun `root suffix receiver preserves implicit Any when absorbing a field-leading semantic delta`() {
        val recv = ai.abstractEmpty                                  // (-1,-1,-2), implicit Any
        val expected = chain(AnyAccessor, mark)                      // (-1,-1,m)
        assertEquals(expected, ai.append(recv, chain(field2, mark)))
        assertEquals(expected, ai.appendFinal(recv, chain(field2, mark)))
    }
    @Test fun `AP@suffix receiver abstracts after retained field for a field-leading exact delta`() {
        val recv = ai.abstractAt(NO_ACCESSOR, i(field), 2)
        assertEquals(recv, ai.appendFinal(recv, chain(field2, FinalAccessor)))
    }
    @Test fun `AP@field receiver rejects a static-leading delta`() {
        val recv = ai.abstractAt(i(stat), NO_ACCESSOR, 1)            // (s,-2,-1), hole at slot 1
        assertNull(ai.appendFinal(recv, chain(stat, mark)))    // delta leads at slot 0
    }
}
