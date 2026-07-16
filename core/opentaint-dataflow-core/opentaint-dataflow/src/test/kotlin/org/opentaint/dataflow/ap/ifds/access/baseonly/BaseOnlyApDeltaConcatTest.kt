package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class BaseOnlyApDeltaConcatTest {
    private val accessors = AccessorInterner()
    private val ai = BaseOnlyAccessOps

    private val field = FieldAccessor("A", "f", "B")
    private val field2 = FieldAccessor("A", "g", "B")
    private val mark = TaintMarkAccessor("m")
    private val stat = ClassStaticAccessor("T")
    private val final = FinalAccessor

    private fun i(a: org.opentaint.dataflow.ap.ifds.Accessor) = accessors.index(a)

    private fun chain(vararg a: org.opentaint.dataflow.ap.ifds.Accessor, abstract: Boolean = false): BaseOnlyAccess =
        ai.build(IntArray(a.size) { i(a[it]) }, abstract)

    @Test
    fun `concat closed fact rejects non-empty delta`() {
        val markFact = chain(mark)
        assertNull(ai.appendFinal(markFact, chain(mark)))
        assertEquals(markFact, ai.appendFinal(markFact, ai.empty))
    }

    @Test
    fun `concat suffix-AP rejects a cross-kind delta`() {
        val f0Abstract = ai.abstractAt(NO_ACCESSOR, i(field), 2)
        val deltaFieldMark = chain(field2, mark)
        assertNull(ai.appendFinal(f0Abstract, deltaFieldMark))
    }

    @Test
    fun `delta requires initial le final`() {
        val c = chain(mark)
        val iValue = chain(final)
        val m = ai.matchPrefix(c, iValue)
        assertFalse(m.emptyDelta)
        assertFalse(m.hasSuffix)
    }

    @Test
    fun `delta abstract initial yields whole final`() {
        val c = chain(mark)
        val m = ai.matchPrefix(c, ai.abstractEmpty)
        assertFalse(m.emptyDelta)
        assertTrue(m.hasSuffix)
        assertEquals(chain(mark), m.suffix)
    }

    @Test
    fun `splitConcreteInitial splits a closed value against a fully abstract final`() {
        val closedInitial = chain(mark)
        val abstractFinal = ai.abstractEmpty
        assertFalse(ai.matchPrefix(abstractFinal, closedInitial).emptyDelta)
        assertFalse(ai.matchPrefix(abstractFinal, closedInitial).hasSuffix)
        val split = ai.splitConcreteInitial(abstractFinal, closedInitial)!!
        assertEquals(abstractFinal, split.matched)
        assertEquals(chain(mark), split.delta)
    }

    @Test
    fun `splitConcreteInitial keeps the tail of a closed field initial past a field-abstract final`() {
        val closedInitial = chain(field, mark)
        val fieldAbstract = ai.abstractAt(NO_ACCESSOR, i(field), 2)
        val split = ai.splitConcreteInitial(fieldAbstract, closedInitial)!!
        assertEquals(fieldAbstract, split.matched)
        assertEquals(chain(mark), split.delta)
    }

    @Test
    fun `splitConcreteInitial rejects abstract initial, concrete final, and prefix mismatch`() {
        assertNull(ai.splitConcreteInitial(ai.abstractEmpty, ai.abstractEmpty))
        assertNull(ai.splitConcreteInitial(chain(mark), chain(mark)))
        assertNull(ai.splitConcreteInitial(ai.abstractAt(NO_ACCESSOR, i(field), 2), chain(field2, mark)))
    }

    @Test
    fun `AP@base wildcard covers every fact`() {
        val apStatic = ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0)
        assertTrue(ai.containsAccess(apStatic, chain(stat, mark)))
        assertTrue(ai.containsAccess(apStatic, chain(mark)))
        assertTrue(ai.containsAccess(apStatic, chain(field, mark)))
    }

    @Test
    fun `AP@suffix empty covers static-less terminals including field-carrying`() {
        val apSuffixEmpty = ai.abstractEmpty
        assertTrue(ai.containsAccess(apSuffixEmpty, chain(mark)))
        assertFalse(ai.containsAccess(apSuffixEmpty, chain(stat, mark)))
        assertTrue(ai.containsAccess(apSuffixEmpty, chain(field, mark)))
    }

    @Test
    fun `AP@suffix with committed field covers that field and bare terminals`() {
        val apSuffixField = ai.abstractAt(NO_ACCESSOR, i(field), 2)
        assertTrue(ai.containsAccess(apSuffixField, chain(field, mark)))
        assertTrue(ai.containsAccess(apSuffixField, chain(mark)))
    }

    @Test
    fun `splitConcreteInitial known-empty field is field-lenient`() {
        val apSuffixEmpty = ai.abstractEmpty
        val fieldSplit = ai.splitConcreteInitial(apSuffixEmpty, chain(field, mark))!!
        assertEquals(apSuffixEmpty, fieldSplit.matched)
        assertEquals(chain(mark), fieldSplit.delta)
        val split = ai.splitConcreteInitial(apSuffixEmpty, chain(mark))!!
        assertEquals(chain(mark), split.delta)
    }

    @Test
    fun `trace append accepts a cross-kind terminal delta at an AP@static prefix`() {
        val apStaticPrefix = ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0)
        val result = ai.append(apStaticPrefix, chain(mark))
        assertNotNull(result)
        assertEquals(chain(mark), result)
    }
}
