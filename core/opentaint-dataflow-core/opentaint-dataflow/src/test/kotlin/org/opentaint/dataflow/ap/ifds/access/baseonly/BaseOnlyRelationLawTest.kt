package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class BaseOnlyRelationLawTest {
    private val interner = AccessorInterner()
    private val stat = interner.index(ClassStaticAccessor("S"))
    private val field = interner.index(FieldAccessor("A", "f", "B"))
    private val otherField = interner.index(FieldAccessor("A", "g", "B"))
    private val mark = interner.index(TaintMarkAccessor("m"))
    private val value = interner.index(ValueAccessor)
    private val any = interner.index(AnyAccessor)
    private val final = interner.index(FinalAccessor)

    private fun access(vararg idx: Int, abstract: Boolean = false): BaseOnlyAccess =
        BaseOnlyAccessOps.build(idx, abstract)

    private val states: List<BaseOnlyAccess> by lazy {
        val normal = access(mark)
        val valueSuffix = access(value, mark)
        listOf(
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0),
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1),
            BaseOnlyAccessOps.abstractEmpty,
            BaseOnlyAccessOps.abstractAt(stat, NO_ACCESSOR, 1),
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, field, 2),
            normal,
            valueSuffix,
            access(any, mark),
            access(field, mark),
            access(otherField, mark),
            access(final),
            access(field, final),
        )
    }

    @Test
    fun `coverage is reflexive and transitive`() {
        for (a in states) assertTrue(BaseOnlyAccessOps.covers(a, a), "not reflexive: $a")
        for (a in states) for (b in states) for (c in states) {
            if (BaseOnlyAccessOps.covers(a, b) && BaseOnlyAccessOps.covers(b, c)) {
                assertTrue(BaseOnlyAccessOps.covers(a, c), "not transitive: $a >= $b >= $c")
            }
        }
    }

    @Test
    fun `overlap is reflexive symmetric and distinct from coverage`() {
        for (a in states) {
            assertTrue(BaseOnlyAccessOps.mayOverlap(a, a), "not reflexive: $a")
            for (b in states) {
                assertTrue(
                    BaseOnlyAccessOps.mayOverlap(a, b) == BaseOnlyAccessOps.mayOverlap(b, a),
                    "not symmetric: $a, $b",
                )
            }
        }

        val bareMark = access(mark)
        val anyMark = access(any, mark)
        val concreteFieldMark = access(field, mark)
        assertTrue(BaseOnlyAccessOps.covers(bareMark, concreteFieldMark))
        assertTrue(BaseOnlyAccessOps.covers(bareMark, anyMark))
        assertTrue(BaseOnlyAccessOps.covers(anyMark, bareMark))
        assertTrue(BaseOnlyAccessOps.covers(anyMark, concreteFieldMark))
        assertFalse(BaseOnlyAccessOps.covers(concreteFieldMark, bareMark))
        assertTrue(BaseOnlyAccessOps.mayOverlap(bareMark, concreteFieldMark))
        assertTrue(BaseOnlyAccessOps.mayOverlap(bareMark, anyMark))
        assertTrue(BaseOnlyAccessOps.mayOverlap(anyMark, concreteFieldMark))

        val normal = access(mark)
        val valueSuffix = access(value, mark)
        val joined = canonicalJoin(normal, valueSuffix)
        assertTrue(joined == setOf(normal, valueSuffix))
        assertFalse(BaseOnlyAccessOps.covers(normal, valueSuffix))
        assertFalse(BaseOnlyAccessOps.covers(valueSuffix, normal))
        assertFalse(BaseOnlyAccessOps.mayOverlap(normal, valueSuffix))
    }
}
