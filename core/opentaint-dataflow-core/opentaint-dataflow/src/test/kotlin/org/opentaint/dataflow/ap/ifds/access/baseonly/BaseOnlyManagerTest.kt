package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
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
}
