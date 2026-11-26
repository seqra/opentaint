package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNull
import kotlin.test.assertTrue

class BaseOnlyFactOpsTest {
    private val arg0 = AccessPathBase.Argument(0)
    private val field = FieldAccessor("A", "f", "B")
    private val field2 = FieldAccessor("A", "g", "B")
    private val mark = TaintMarkAccessor("m")
    private val stat = ClassStaticAccessor("T")
    private val typeInfo = TypeInfoAccessor("pkg.fn")

    private fun mgr(fieldSensitive: Boolean) =
        BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, org.opentaint.dataflow.util.Cancellation(), fieldSensitive = fieldSensitive)

    private fun BaseOnlyApManager.finalOf(vararg accessors: Accessor): BaseOnlyFinalFactAp {
        var f = createFinalAp(arg0, ExclusionSet.Empty) as BaseOnlyFinalFactAp
        accessors.reversed().forEach { f = f.prependAccessor(it) as BaseOnlyFinalFactAp }
        return f
    }

    @Test
    fun `md0 prepend field is absorbed`() {
        val m = mgr(false)
        val argMark = m.finalOf(AnyAccessor, mark)
        assertEquals(argMark, argMark.prependAccessor(field))
    }

    @Test
    fun `md0 read field returns self`() {
        val m = mgr(false)
        val argMark = m.finalOf(AnyAccessor, mark)
        assertEquals(argMark, argMark.readAccessor(field))
    }

    @Test
    fun `md0 starts with field is true`() {
        val m = mgr(false)
        val argMark = m.finalOf(AnyAccessor, mark)
        assertTrue(argMark.startsWithAccessor(field))
    }

    @Test
    fun `md1 prepend field is kept before any`() {
        val m = mgr(true)
        val argMark = m.finalOf(AnyAccessor, mark)
        assertEquals(m.finalOf(field, AnyAccessor, mark), argMark.prependAccessor(field))
    }

    @Test
    fun `md1 second field replaces first`() {
        val m = mgr(true)
        val argFieldMark = m.finalOf(field, AnyAccessor, mark)
        assertEquals(m.finalOf(field2, AnyAccessor, mark), argFieldMark.prependAccessor(field2))
    }

    @Test
    fun `md1 read matching field consumes it`() {
        val m = mgr(true)
        val argFieldMark = m.finalOf(field, AnyAccessor, mark)
        assertEquals(m.finalOf(AnyAccessor, mark), argFieldMark.readAccessor(field))
    }

    @Test
    fun `md1 read non matching field is null`() {
        val m = mgr(true)
        val argFieldMark = m.finalOf(field, AnyAccessor, mark)
        assertNull(argFieldMark.readAccessor(field2))
    }

    @Test
    fun `plain semantic fact has an implicit structural branch`() {
        val m = mgr(false)
        val argMark = m.finalOf(mark)
        assertTrue(argMark.startsWithAccessor(field))
        assertTrue(argMark.startsWithAccessor(mark))
        assertEquals(argMark, argMark.readAccessor(field))
    }

    @Test
    fun `a concrete clear does not consume the implicit Any branch`() {
        val m = mgr(false)
        val argMark = m.finalOf(AnyAccessor, mark)
        assertEquals(argMark, argMark.clearAccessor(field))
    }

    @Test
    fun `start accessors expose any and the head for a semantic mark`() {
        val m = mgr(false)
        assertEquals(
            setOf<Accessor>(AnyAccessor, mark),
            m.finalOf(AnyAccessor, mark).getStartAccessors(),
        )
        assertEquals(
            setOf<Accessor>(AnyAccessor, mark),
            m.finalOf(mark).getStartAccessors(),
        )
        assertEquals(setOf<Accessor>(FinalAccessor), m.finalOf().getStartAccessors())
    }

    @Test
    fun `start accessors expose the structural head before a semantic mark`() {
        val m = mgr(true)
        assertEquals(
            setOf<Accessor>(field),
            m.finalOf(field, AnyAccessor, mark).getStartAccessors(),
        )
    }

    @Test
    fun `static kept before field on both fact sides`() {
        val m = mgr(true)
        val expected = m.finalOf(stat, field, AnyAccessor, mark)
        val actual = m.finalOf(field, AnyAccessor, mark).prependAccessor(stat)
        assertEquals(expected, actual)
    }

    @Test
    fun `value type wrapper is distinct and group read exposes the normal residual`() {
        val m = mgr(true)
        val typed = m.finalOf(TypeInfoGroupAccessor, typeInfo)
        assertFalse(m.finalOf(typeInfo) == typed)
        assertTrue(typed.startsWithAccessor(TypeInfoGroupAccessor))
        val residual = typed.readAccessor(TypeInfoGroupAccessor)!!
        assertEquals(m.finalOf(typeInfo), residual)
        assertEquals(
            setOf<Accessor>(AnyAccessor, typeInfo),
            residual.getStartAccessors(),
        )
        assertEquals(typed, typed.clearAccessor(TypeInfoGroupAccessor))
        assertEquals(typed, typed.clearAccessor(typeInfo))
    }

    @Test
    fun `type info fact enumerates as the collapsed group-type pair`() {
        val m = mgr(true)
        val typed = m.finalOf(TypeInfoGroupAccessor, typeInfo)
        assertEquals(1, typed.size)
        assertEquals(
            setOf<Accessor>(TypeInfoGroupAccessor, typeInfo, FinalAccessor),
            typed.getAllAccessors(),
        )
    }

    @Test
    fun `value accessor states have exact read and clear behavior`() {
        val m = mgr(true)
        val directMark = m.finalOf(mark)
        val valueMark = m.finalOf(ValueAccessor, mark)
        assertEquals(setOf<Accessor>(AnyAccessor, mark), directMark.getStartAccessors())
        assertEquals(setOf<Accessor>(AnyAccessor, ValueAccessor), valueMark.getStartAccessors())
        assertEquals(directMark, valueMark.readAccessor(ValueAccessor))
        assertEquals(directMark, directMark.clearAccessor(mark))
        assertEquals(valueMark, valueMark.clearAccessor(ValueAccessor))

        val directType = m.finalOf(typeInfo)
        val groupedType = m.finalOf(TypeInfoGroupAccessor, typeInfo)
        assertEquals(setOf<Accessor>(AnyAccessor, typeInfo), directType.getStartAccessors())
        assertEquals(setOf<Accessor>(AnyAccessor, TypeInfoGroupAccessor), groupedType.getStartAccessors())
        assertEquals(directType, groupedType.readAccessor(TypeInfoGroupAccessor))
        assertEquals(directType, directType.clearAccessor(typeInfo))
        assertEquals(groupedType, groupedType.clearAccessor(TypeInfoGroupAccessor))
    }

    @Test
    fun `type info group is absent without a type accessor`() {
        val m = mgr(false)
        val plain = m.finalOf(mark)
        assertFalse(plain.startsWithAccessor(TypeInfoGroupAccessor))
        assertNull(plain.readAccessor(TypeInfoGroupAccessor))
    }

    @Test
    fun `initial fact ops mirror final`() {
        val m = mgr(true)
        var i = m.createFinalInitialAp(arg0, ExclusionSet.Empty) as BaseOnlyInitialFactAp
        i = i.prependAccessor(mark) as BaseOnlyInitialFactAp
        i = i.prependAccessor(AnyAccessor) as BaseOnlyInitialFactAp
        assertTrue(i.startsWithAccessor(field))
    }
}
