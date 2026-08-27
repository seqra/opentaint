package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.AnyMatchMode
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals

/**
 * The literal/denotational `[any]` decision is ONE global option, and a per-instance choice wins.
 *
 * Both halves were broken. The exact cleaner parsed the property on its own file, where no manager
 * could reach it; and the `.part` bisect rungs consulted a JVM-wide property IN PREFERENCE TO the
 * constructor argument, so a manager deliberately built in the other mode could be silently pulled
 * back by a `-D` its caller never set.
 */
class AnyMatchModeTest {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private fun manager(literalAnyMatch: Boolean) =
        TreeApManager(UnrollStrategy, RefManager(), Cancellation(), -1, literalAnyMatch = literalAnyMatch)

    @Test
    fun `the manager's default is the one global option`() {
        assertEquals(
            AnyMatchMode.literal, TreeApManager.DEFAULT_LITERAL_ANY_MATCH,
            "one property, one parse -- the manager must not have its own copy"
        )
    }

    @Test
    fun `the exact cleaner follows the same option`() {
        // Not `assertEquals(AnyMatchMode.literal, ...)`: `-Dopentaint.exactCleanerKeepsAny` exists to
        // break the tie deliberately. What must hold is that the DEFAULT is the mode and not a
        // separately parsed copy of the same property.
        val expected = AnyMatchMode.boolProperty("opentaint.exactCleanerKeepsAny") ?: AnyMatchMode.literal
        assertEquals(expected, AnyMatchMode.exactCleanerKeepsAny)
    }

    /**
     * The precedence rule, pinned in the direction that was inverted: whatever `.part` properties
     * this JVM happens to carry, a manager constructed AGAINST the global default gets exactly what
     * it asked for in all five channels.
     */
    @Test
    fun `an explicit per-instance mode beats every part property`() {
        val against = !TreeApManager.DEFAULT_LITERAL_ANY_MATCH
        val m = manager(against)

        assertEquals(against, m.literalAnyMatch)
        assertEquals(against, m.literalAnyReader, "reader")
        assertEquals(against, m.literalAnyLookup, "lookup")
        assertEquals(against, m.literalAnyPremises, "premises")
        assertEquals(against, m.dropR3c, "premises.r3c")
        assertEquals(against, m.dropR4, "premises.r4")
    }

    /** And the agreeing direction still resolves, so the bisect rungs stay usable. */
    @Test
    fun `a manager at the global default resolves each part`() {
        val wide = TreeApManager.DEFAULT_LITERAL_ANY_MATCH
        val m = manager(wide)

        assertEquals(AnyMatchMode.part("reader") ?: wide, m.literalAnyReader)
        assertEquals(AnyMatchMode.part("lookup") ?: wide, m.literalAnyLookup)
        assertEquals(AnyMatchMode.part("premises") ?: wide, m.literalAnyPremises)
    }

    /**
     * The rung chain survives a rung being set.
     *
     * The precedence test is the CONSTRUCTOR ARGUMENT against the global option, not each
     * intermediate value against it -- otherwise `-Dopentaint.literalAnyMatch.premises=false` would
     * push `literalAnyPremises` off the global default and make the two rungs BENEATH it
     * unreachable, silently disabling the finest half of the ladder.
     */
    @Test
    fun `a finer rung still resolves under a coarser one`() {
        val wide = TreeApManager.DEFAULT_LITERAL_ANY_MATCH
        val m = manager(wide)

        assertEquals(AnyMatchMode.part("premises.r3c") ?: m.literalAnyPremises, m.dropR3c)
        assertEquals(AnyMatchMode.part("premises.r4") ?: m.literalAnyPremises, m.dropR4)
    }
}
