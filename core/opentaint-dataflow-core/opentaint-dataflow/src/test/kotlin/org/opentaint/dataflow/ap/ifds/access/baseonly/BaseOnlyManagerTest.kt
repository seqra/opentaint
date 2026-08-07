package org.opentaint.dataflow.ap.ifds.access.baseonly

import kotlinx.collections.immutable.PersistentSet
import kotlinx.collections.immutable.persistentHashSetOf
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class BaseOnlyManagerTest {
    private val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, Cancellation())

    private object Seam : BaseOnlyFinalApAccess {
        lateinit var mgr: BaseOnlyApManager
        override val apManager: BaseOnlyApManager get() = mgr
    }

    @Test
    fun `create final ap carries final accessor`() {
        val f = manager.createFinalAp(AccessPathBase.This, ExclusionSet.Empty) as BaseOnlyFinalFactAp
        assertEquals(AccessPathBase.This, f.base)
        assertEquals(1, f.size)
        assertFalse(f.isAbstract())
    }

    @Test
    fun `most abstract final ap is abstract`() {
        val f = manager.mostAbstractFinalAp(AccessPathBase.This) as BaseOnlyFinalFactAp
        assertTrue(f.isAbstract())
        assertEquals(0, f.size)
    }

    @Test
    fun `most abstract initial ap is abstract`() {
        val f = manager.mostAbstractInitialAp(AccessPathBase.This) as BaseOnlyInitialFactAp
        assertTrue(f.isAbstract())
        assertEquals(0, f.size)
    }

    @Test
    fun `create final initial ap carries final accessor`() {
        val f = manager.createFinalInitialAp(AccessPathBase.This, ExclusionSet.Empty) as BaseOnlyInitialFactAp
        assertEquals(1, f.size)
        assertFalse(f.isAbstract())
    }

    @Test
    fun `seam round trips final fact`() {
        Seam.mgr = manager
        val access = BaseOnlyAccessOps.abstractEmpty
        val f = Seam.createFinal(AccessPathBase.This, access, ExclusionSet.Empty)
        assertEquals(access, Seam.getFinalAccess(f))
    }

    @Test
    fun `BaseOnly facts compact exclusions without changing their set algebra`() {
        val first = TaintMarkAccessor("first")
        val second = TaintMarkAccessor("second")
        val third = TaintMarkAccessor("third")
        val original = ExclusionSet.Concrete(persistentHashSetOf(first, second))

        val fact = manager.createFinalAp(AccessPathBase.This, original) as BaseOnlyFinalFactAp
        val compact = fact.exclusions as ExclusionSet.Concrete

        assertEquals(original, compact)
        assertEquals(original.hashCode(), compact.hashCode())
        assertFalse(compact.set is PersistentSet<*>)
        assertEquals(
            ExclusionSet.Concrete(persistentHashSetOf(first, second, third)),
            compact.add(third),
        )
        assertEquals(
            ExclusionSet.Concrete(second),
            compact.intersect(ExclusionSet.Concrete(persistentHashSetOf(second, third))),
        )
        assertEquals(
            ExclusionSet.Concrete(first),
            compact.subtract(ExclusionSet.Concrete(second)),
        )

    }

    @Test
    fun `compact exclusion algebra agrees with persistent sets`() {
        val accessors = List(5) { TaintMarkAccessor("exclusion-$it") }
        fun exclusions(mask: Int): ExclusionSet = if (mask == 0) {
            ExclusionSet.Empty
        } else {
            ExclusionSet.Concrete(
                persistentHashSetOf(*accessors.filterIndexed { index, _ -> mask and (1 shl index) != 0 }.toTypedArray())
            )
        }
        fun compact(exclusions: ExclusionSet): ExclusionSet =
            manager.createFinalAp(AccessPathBase.This, exclusions).exclusions

        for (leftMask in 0 until (1 shl accessors.size)) {
            val left = exclusions(leftMask)
            val compactLeft = compact(left)
            assertEquals(left, compactLeft)
            assertEquals(left.hashCode(), compactLeft.hashCode())

            accessors.forEach { accessor ->
                assertEquals(left.add(accessor), compactLeft.add(accessor))
                assertEquals(left.subtract(accessor), compactLeft.subtract(accessor))
            }

            for (rightMask in 0 until (1 shl accessors.size)) {
                val right = exclusions(rightMask)
                val compactRight = compact(right)
                assertEquals(left.union(right), compactLeft.union(compactRight))
                assertEquals(left.intersect(right), compactLeft.intersect(compactRight))
                if (compactLeft is ExclusionSet.Concrete && compactRight is ExclusionSet.Concrete) {
                    assertEquals(
                        (left as ExclusionSet.Concrete).subtract(right as ExclusionSet.Concrete),
                        compactLeft.subtract(compactRight),
                    )
                    val update =
                        (compactLeft.set as BaseOnlyExclusionAccessorSet)
                            .unionWithAdded(compactRight.set as BaseOnlyExclusionAccessorSet)
                    val expectedAdded =
                        (right as ExclusionSet.Concrete).subtract(left as ExclusionSet.Concrete)
                    if (expectedAdded is ExclusionSet.Empty) {
                        assertEquals(null, update)
                    } else {
                        assertEquals(left.union(right), ExclusionSet.Concrete(checkNotNull(update).union))
                        assertEquals(expectedAdded, ExclusionSet.Concrete(update.added))
                    }
                }
            }
        }
    }
}
