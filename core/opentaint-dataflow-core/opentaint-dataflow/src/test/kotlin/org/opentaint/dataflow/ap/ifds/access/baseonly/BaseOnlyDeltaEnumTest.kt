package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class BaseOnlyDeltaEnumTest {
    private val accessors = AccessorInterner()
    private val ai = BaseOnlyAccessOps
    private val field = FieldAccessor("A", "f", "B")
    private val mark = TaintMarkAccessor("m")
    private val stat = ClassStaticAccessor("T")
    private fun i(a: org.opentaint.dataflow.ap.ifds.Accessor) = accessors.index(a)
    private fun chain(vararg a: org.opentaint.dataflow.ap.ifds.Accessor, abstract: Boolean = false): BaseOnlyAccess =
        ai.build(IntArray(a.size) { i(a[it]) }, abstract)

    private fun assertDelta(context: BaseOnlyAccess, pattern: BaseOnlyAccess, expected: BaseOnlyAccess) {
        val m = ai.matchPrefix(context, pattern)
        assertTrue(m.hasSuffix, "expected a delta for context=$context pattern=$pattern")
        assertFalse(m.emptyDelta)
        assertEquals(expected, m.suffix, "wrong delta for context=$context pattern=$pattern")
    }
    private fun assertIdentity(a: BaseOnlyAccess) {
        val m = ai.matchPrefix(a, a)
        assertTrue(m.emptyDelta); assertFalse(m.hasSuffix)
    }
    private fun assertNoMatch(context: BaseOnlyAccess, pattern: BaseOnlyAccess) {
        val m = ai.matchPrefix(context, pattern)
        assertFalse(m.hasSuffix, "expected NO_MATCH for context=$context pattern=$pattern")
        assertFalse(m.emptyDelta)
    }

    // canonical shapes
    private val apStatic get() = ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0)          // (-2,-1,-1)
    private val apFieldNoStat get() = ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1)     // (-1,-2,-1)
    private val apFieldStat get() = ai.abstractAt(i(stat), NO_ACCESSOR, 1)           // (s1,-2,-1)
    private val apSuffixEmpty get() = ai.abstractEmpty                                // (-1,-1,-2)
    private val apSuffixStat get() = ai.abstractAt(i(stat), NO_ACCESSOR, 2)          // (s1,-1,-2)
    private val apSuffixField get() = ai.abstractAt(NO_ACCESSOR, i(field), 2)        // (-1,f1,-2)

    @Test fun `AP@static covers static-carrying, delta is the whole static fact`() {
        assertDelta(chain(stat, mark), apStatic, chain(stat, mark))     // (s,-1,t) -> whole
        assertIdentity(apStatic)
    }
    @Test fun `AP@static does NOT cover a static-less fact`() {
        assertNoMatch(chain(mark), apStatic)                            // (-1,-1,t)
        assertNoMatch(chain(field, mark), apStatic)                     // (-1,f,t)
    }
    @Test fun `AP@field with static committed yields field-leading delta`() {
        assertDelta(chain(stat, field, mark), apFieldStat, chain(field, mark)) // (s,f,t) -> (-1,f,t)
        assertIdentity(apFieldStat)
    }
    @Test fun `AP@field with static committed rejects wrong or missing static`() {
        assertNoMatch(chain(field, mark), apFieldStat)                  // no static
    }
    @Test fun `AP@field no-static yields field-leading delta`() {
        assertDelta(chain(field, mark), apFieldNoStat, chain(field, mark))     // (-1,f,t) -> (-1,f,t)
        assertNoMatch(chain(stat, field, mark), apFieldNoStat)                 // known-empty static strict
    }
    @Test fun `AP@suffix empty yields terminal-leading delta and rejects static or field facts`() {
        assertDelta(chain(mark), apSuffixEmpty, chain(mark))            // (-1,-1,t) -> (-1,-1,t)
        assertNoMatch(chain(stat, mark), apSuffixEmpty)                 // known-empty static strict
        assertNoMatch(chain(field, mark), apSuffixEmpty)               // known-empty field strict
        assertIdentity(apSuffixEmpty)
    }
    @Test fun `AP@suffix with static committed yields terminal-leading delta`() {
        assertDelta(chain(stat, mark), apSuffixStat, chain(mark))       // (s,-1,t) -> (-1,-1,t)
        assertNoMatch(chain(mark), apSuffixStat)                        // missing static
    }
    @Test fun `AP@suffix with field committed yields terminal-leading delta`() {
        assertDelta(chain(field, mark), apSuffixField, chain(mark))     // (-1,f,t) -> (-1,-1,t)
        assertNoMatch(chain(mark), apSuffixField)                       // missing field
    }
    @Test fun `concrete pattern never yields a delta`() {
        assertNoMatch(chain(mark), chain(FinalAccessor))               // initial has no AP
    }
}
