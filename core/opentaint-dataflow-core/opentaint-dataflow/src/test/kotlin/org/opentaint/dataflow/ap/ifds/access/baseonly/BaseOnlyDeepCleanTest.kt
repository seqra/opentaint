package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNull
import kotlin.test.assertSame

// Pin for BaseOnlyFinalFactAp.clearAllAccessorOccurrences, the BaseOnly implementation of the
// upstream deep accessor exclusion. The reference is docs/baseonly-deep-accessor-exclusion-design.md
// section 4: the outcome is decided by whether the fact's terminal is the cleaned mark and by
// `pastFirst`, an occupied static or field slot proving the terminal sits at position >= 2.
//
// Rows where the two modes disagree are the inherent field-insensitivity widening, not defects:
// mode 0 never installs a field slot, so it cannot prove position >= 2 and must keep a fact that
// mode 1 deletes. Keeping a fact is a false positive, which is the safe direction.
class BaseOnlyDeepCleanTest {
    private val base = AccessPathBase.Argument(0)
    private val field = FieldAccessor("C", "f", "T")
    private val static = ClassStaticAccessor("S")
    private val mark = TaintMarkAccessor("tainted")
    private val otherMark = TaintMarkAccessor("other")

    private fun manager(fieldSensitive: Boolean) =
        BaseOnlyApManager(
            AnyAccessorUnrollStrategy.AnyAccessorDisabled,
            Cancellation(),
            fieldSensitive = fieldSensitive,
        )

    private fun BaseOnlyApManager.fact(vararg accessors: org.opentaint.dataflow.ap.ifds.Accessor): FinalFactAp {
        var result = createFinalAp(base, ExclusionSet.Empty)
        accessors.reversed().forEach { result = result.prependAccessor(it) }
        return result
    }

    @Test
    fun `a terminal mark is removed at every position when the start is not kept`() {
        for (fieldSensitive in listOf(false, true)) {
            val mgr = manager(fieldSensitive)
            assertNull(
                mgr.fact(mark).clearAllAccessorOccurrences(mark, keepStartAccessor = false),
                "fieldSensitive=$fieldSensitive: every denoted path ends in the mark",
            )
            assertNull(
                mgr.fact(field, mark).clearAllAccessorOccurrences(mark, keepStartAccessor = false),
                "fieldSensitive=$fieldSensitive: every denoted path ends in the mark",
            )
        }
    }

    @Test
    fun `a root terminal mark survives when the start is kept`() {
        for (fieldSensitive in listOf(false, true)) {
            val mgr = manager(fieldSensitive)
            val fact = mgr.fact(mark)
            assertSame(
                fact,
                fact.clearAllAccessorOccurrences(mark, keepStartAccessor = true),
                "fieldSensitive=$fieldSensitive: the mark may sit at position 1, so it is spared",
            )
        }
    }

    @Test
    fun `an occupied field slot proves the mark is past the first position`() {
        val fieldInsensitive = manager(fieldSensitive = false)
        val kept = fieldInsensitive.fact(field, mark)
        assertSame(
            kept,
            kept.clearAllAccessorOccurrences(mark, keepStartAccessor = true),
            "mode 0 absorbs the field, so it cannot prove position >= 2 and must widen",
        )

        val fieldSensitive = manager(fieldSensitive = true)
        assertNull(
            fieldSensitive.fact(field, mark).clearAllAccessorOccurrences(mark, keepStartAccessor = true),
            "mode 1 retains the field, which proves the mark is at position >= 2",
        )
    }

    @Test
    fun `an occupied static slot proves the mark is past the first position`() {
        for (fieldSensitive in listOf(false, true)) {
            val mgr = manager(fieldSensitive)
            assertNull(
                mgr.fact(static, mark).clearAllAccessorOccurrences(mark, keepStartAccessor = true),
                "fieldSensitive=$fieldSensitive: the static accessor itself consumed position 1",
            )
        }
    }

    @Test
    fun `a different mark is left alone`() {
        for (fieldSensitive in listOf(false, true)) {
            val mgr = manager(fieldSensitive)
            for (keepStart in listOf(false, true)) {
                val fact = mgr.fact(field, otherMark)
                assertSame(
                    fact,
                    fact.clearAllAccessorOccurrences(mark, keepStartAccessor = keepStart),
                    "fieldSensitive=$fieldSensitive keepStart=$keepStart: marks are terminal-only",
                )
            }
        }
    }

    @Test
    fun `an abstract fact is annotated rather than dropped`() {
        for (fieldSensitive in listOf(false, true)) {
            val mgr = manager(fieldSensitive)
            for (keepStart in listOf(false, true)) {
                val abstract = mgr.mostAbstractFinalAp(base)
                assertEquals(
                    abstract,
                    abstract.clearAllAccessorOccurrences(mark, keepStartAccessor = keepStart),
                    "fieldSensitive=$fieldSensitive keepStart=$keepStart: nothing is materialized below yet",
                )
            }
        }
    }

    @Test
    fun `cleaning a non-mark accessor is rejected rather than answered wrongly`() {
        val mgr = manager(fieldSensitive = true)
        assertFailsWith<NotImplementedError> {
            mgr.fact(field, mark).clearAllAccessorOccurrences(field, keepStartAccessor = true)
        }
    }
}
