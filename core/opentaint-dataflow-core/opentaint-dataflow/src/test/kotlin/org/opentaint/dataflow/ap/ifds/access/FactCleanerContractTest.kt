package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.automata.AutomataApManager
import org.opentaint.dataflow.ap.ifds.access.cactus.CactusApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class FactCleanerContractTest {
    private val base = AccessPathBase.This
    private val field = FieldAccessor("Box", "value", "String")
    private val mark = TaintMarkAccessor("tainted")

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = false
    }

    private fun managers(): List<ApManager> = listOf(
        TreeApManager(UnrollStrategy, RefManager(), Cancellation()),
        AutomataApManager(UnrollStrategy, Cancellation()),
        CactusApManager(UnrollStrategy, Cancellation()),
    )

    @Test
    fun `every representation implements the same cleaner boundary`() {
        for (manager in managers()) {
            assertEquals(
                1,
                manager.mostAbstractFinalAp(base)
                    .clean(listOf(AnyAccessor, mark))
                    .survivingFacts.size,
                "${manager::class.simpleName} must preserve a cleaned abstract fact",
            )

            var concrete = manager.createFinalAp(base, ExclusionSet.Empty)
            for (accessor in listOf(field, mark).asReversed()) {
                concrete = concrete.prependAccessor(accessor)
            }

            val cleanResult = concrete.clean(listOf(AnyAccessor, mark))
            assertTrue(
                cleanResult.survivingFacts.isEmpty() ||
                    cleanResult.survivingFacts.none {
                        it.readAccessor(field)?.startsWithAccessor(mark) == true
                    },
                "${manager::class.simpleName} retained an already-materialized nested mark",
            )
        }
    }

    @Test
    fun `plain and any-field cleaners use the same operation`() {
        for (manager in managers()) {
            var concrete = manager.createFinalAp(base, ExclusionSet.Empty)
            for (accessor in listOf(field, mark).asReversed()) {
                concrete = concrete.prependAccessor(accessor)
            }

            val plain = concrete.clean(listOf(field, mark))
            val anyField = concrete.clean(listOf(AnyAccessor, mark))

            assertTrue(plain.survivingFacts.isEmpty())
            assertTrue(anyField.survivingFacts.isEmpty())
        }
    }
}
