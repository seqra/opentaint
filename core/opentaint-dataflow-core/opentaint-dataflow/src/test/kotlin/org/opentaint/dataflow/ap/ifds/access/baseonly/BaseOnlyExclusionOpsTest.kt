package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertSame
import kotlin.test.assertTrue

class BaseOnlyExclusionOpsTest {
    private val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, fieldSensitive = true)
    private val interner get() = manager.interner

    private val s1 = ClassStaticAccessor("S1")
    private val f1 = FieldAccessor("C", "f1", "T")
    private val t1 = TaintMarkAccessor("t1")
    private val ty1 = TypeInfoAccessor("pkg.Ty1")

    private fun ex(vararg accessors: Accessor): ExclusionSet =
        accessors.fold(ExclusionSet.Empty as ExclusionSet) { acc, a -> acc.add(a) }

    @Test
    fun `empty and universe map to sentinels and back`() {
        assertSame(BaseOnlyExclusion.EMPTY, BaseOnlyExclusionOps.fromExclusionSet(ExclusionSet.Empty, interner, 0))
        assertSame(BaseOnlyExclusion.UNIVERSE, BaseOnlyExclusionOps.fromExclusionSet(ExclusionSet.Universe, interner, 0))
        assertEquals(ExclusionSet.Empty, BaseOnlyExclusionOps.toExclusionSet(BaseOnlyExclusion.EMPTY, interner))
        assertEquals(ExclusionSet.Universe, BaseOnlyExclusionOps.toExclusionSet(BaseOnlyExclusion.UNIVERSE, interner))
    }

    @Test
    fun `lossless round-trip at apSlot 0`() {
        val e = ex(s1, f1, t1, ty1)
        val compact = BaseOnlyExclusionOps.fromExclusionSet(e, interner, 0)
        assertEquals(e, BaseOnlyExclusionOps.toExclusionSet(compact, interner))
    }

    @Test
    fun `N floor drops accessors below the initial apSlot`() {
        val e = ex(s1, f1, t1)
        assertEquals(
            ex(f1, t1),
            BaseOnlyExclusionOps.toExclusionSet(BaseOnlyExclusionOps.fromExclusionSet(e, interner, 1), interner),
        )
        assertEquals(
            ex(t1),
            BaseOnlyExclusionOps.toExclusionSet(BaseOnlyExclusionOps.fromExclusionSet(e, interner, 2), interner),
        )
    }

    @Test
    fun `filtered-to-empty canonicalizes to EMPTY sentinel`() {
        assertSame(BaseOnlyExclusion.EMPTY, BaseOnlyExclusionOps.fromExclusionSet(ex(s1), interner, 1))
    }

    @Test
    fun `contains reflects membership with type-info-group fallback`() {
        val onlyGroup = BaseOnlyExclusionOps.fromExclusionSet(ex(TypeInfoGroupAccessor), interner, 0)
        assertTrue(BaseOnlyExclusionOps.contains(onlyGroup, interner.index(ty1)))
        assertTrue(BaseOnlyExclusionOps.contains(onlyGroup, TYPE_INFO_GROUP_ACCESSOR_IDX))
        assertFalse(BaseOnlyExclusionOps.contains(onlyGroup, interner.index(f1)))
        assertFalse(BaseOnlyExclusionOps.contains(BaseOnlyExclusion.EMPTY, interner.index(f1)))
        assertTrue(BaseOnlyExclusionOps.contains(BaseOnlyExclusion.UNIVERSE, interner.index(f1)))
    }

    @Test
    fun `mergeInPlace unions and reports growth`() {
        val a = BaseOnlyExclusionOps.fromExclusionSet(ex(f1), interner, 0)
        val b = BaseOnlyExclusionOps.fromExclusionSet(ex(t1), interner, 0)
        val m1 = BaseOnlyExclusionOps.mergeInPlace(a, b)
        assertTrue(m1.grew)
        assertEquals(ex(f1, t1), BaseOnlyExclusionOps.toExclusionSet(m1.value, interner))
        val m2 = BaseOnlyExclusionOps.mergeInPlace(m1.value, BaseOnlyExclusionOps.fromExclusionSet(ex(f1), interner, 0))
        assertFalse(m2.grew)
    }

    @Test
    fun `mergeInPlace universe absorbs and empty is a no-op`() {
        val a = BaseOnlyExclusionOps.fromExclusionSet(ex(f1), interner, 0)
        assertFalse(BaseOnlyExclusionOps.mergeInPlace(a, BaseOnlyExclusion.EMPTY).grew)
        val u = BaseOnlyExclusionOps.mergeInPlace(a, BaseOnlyExclusion.UNIVERSE)
        assertTrue(u.grew)
        assertSame(BaseOnlyExclusion.UNIVERSE, u.value)
        assertFalse(BaseOnlyExclusionOps.mergeInPlace(BaseOnlyExclusion.UNIVERSE, a).grew)
    }
}
