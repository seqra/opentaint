package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.configuration.CommonTaintAssignAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertTrue

class TaintSourceActionPreconditionEvaluatorTest {
    private val base = AccessPathBase.This
    private val mark = TaintMarkAccessor("tainted")

    private object Rule : CommonTaintConfigurationItem
    private object Action : CommonTaintAssignAction

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = false
    }

    private fun evaluator(): TaintSourceActionPreconditionEvaluator {
        val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())
        val demandedFact = manager.mkInitialAccessPath(
            PositionAccess.Simple(base).withSuffix(listOf(AnyAccessor, mark)),
            ExclusionSet.Universe,
        )
        return TaintSourceActionPreconditionEvaluator(InitialFactReader(demandedFact, manager))
    }

    @Test
    fun `exact source cannot explain a demanded property`() {
        val result = evaluator().evaluateProducedFact(
            Rule,
            Action,
            PositionAccess.Simple(base),
            mark,
        )

        assertTrue(result.isNone)
    }

    @Test
    fun `AnyField source can explain a demanded property`() {
        val result = evaluator().evaluateProducedFact(
            Rule,
            Action,
            PositionAccess.Simple(base).withSuffix(listOf(AnyAccessor)),
            mark,
        )

        assertTrue(result.isSome)
    }
}
