package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.automata.AutomataApManager
import org.opentaint.dataflow.ap.ifds.access.cactus.CactusApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertIs
import kotlin.test.assertTrue

class DeepCleanContractTest {
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
    fun `every representation implements the same deep-clean boundary`() {
        for (manager in managers()) {
            assertIs<FinalFactAp.DeepCleanResult.Cleaned>(
                manager.mostAbstractFinalAp(base).deepClean(mark),
                "${manager::class.simpleName} must preserve a cleaned abstract fact",
            )

            var concrete = manager.createFinalAp(base, ExclusionSet.Empty)
            for (accessor in listOf(field, mark).asReversed()) {
                concrete = concrete.prependAccessor(accessor)
            }

            val cleanResult = concrete.deepClean(mark)
            assertTrue(
                cleanResult is FinalFactAp.DeepCleanResult.RemovedCompletely ||
                    cleanResult is FinalFactAp.DeepCleanResult.Cleaned &&
                    cleanResult.fact.readAccessor(field)?.startsWithAccessor(mark) != true,
                "${manager::class.simpleName} retained an already-materialized nested mark",
            )
        }
    }
}
