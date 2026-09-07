package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class BaseOnlyAnyMatchTest {
    private val arg0 = AccessPathBase.Argument(0)
    private val mark = TaintMarkAccessor("m")
    private val field = FieldAccessor("A", "f", "B")

    private fun mgr(fieldSensitive: Boolean = false) =
        BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, Cancellation(), fieldSensitive = fieldSensitive)

    private fun BaseOnlyApManager.expandedTainted(): FinalFactAp =
        createFinalAp(arg0, ExclusionSet.Empty).prependAccessor(mark).prependAccessor(AnyAccessor)

    private fun BaseOnlyApManager.finalSinkReq(): InitialFactAp =
        createFinalInitialAp(arg0, ExclusionSet.Empty).prependAccessor(mark)

    private fun BaseOnlyApManager.abstractSinkReq(): InitialFactAp =
        mostAbstractInitialAp(arg0).prependAccessor(mark)

    @Test
    fun `any-expanded fact satisfies value-itself sink requirement with final accessor`() {
        val m = mgr()
        val f = m.expandedTainted()
        val req = m.finalSinkReq()
        assertTrue(
            f.contains(req),
            "expanded ${(f as BaseOnlyFinalFactAp).access} must contain sink ${(req as BaseOnlyInitialFactAp).access}",
        )
    }

    @Test
    fun `any-expanded fact satisfies abstract value-itself sink requirement`() {
        val m = mgr()
        val f = m.expandedTainted()
        assertTrue(f.contains(m.abstractSinkReq()))
    }

    @Test
    fun `field-qualified requirement is covered because fields are absorbed`() {
        val m = mgr()
        val f = m.expandedTainted()
        val req = m.createFinalInitialAp(arg0, ExclusionSet.Empty).prependAccessor(mark).prependAccessor(field)
        assertTrue(
            f.contains(req),
            "value fact ${(f as BaseOnlyFinalFactAp).access} must cover field req ${(req as BaseOnlyInitialFactAp).access}",
        )
    }

    @Test
    fun `expanded fact does not spuriously match a different mark`() {
        val m = mgr()
        val f = m.expandedTainted()
        val other = m.createFinalInitialAp(arg0, ExclusionSet.Empty).prependAccessor(TaintMarkAccessor("other"))
        assertFalse(f.contains(other))
    }

    @Test
    fun `expanded fact starts with its terminal mark`() {
        val m = mgr()
        assertTrue((m.expandedTainted() as BaseOnlyFinalFactAp).let { it.startsWithAccessor(mark) || it.startsWithAccessor(AnyAccessor) })
        assertTrue((m.expandedTainted() as BaseOnlyFinalFactAp).startsWithAccessor(mark))
    }

    @Test
    fun `startsWith implies readAccessor is non-null`() {
        val m = mgr()
        val f = m.expandedTainted()
        for (accessor in listOf(mark, field, AnyAccessor)) {
            if (f.startsWithAccessor(accessor)) {
                assertTrue(f.readAccessor(accessor) != null, "startsWith($accessor) but readAccessor null")
            }
        }
        for (accessor in (f as BaseOnlyFinalFactAp).getStartAccessors()) {
            assertTrue(f.readAccessor(accessor) != null, "readAccessor(startAccessor $accessor) null")
        }
    }
}
