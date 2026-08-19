package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.Test
import kotlin.test.assertEquals
import org.opentaint.dataflow.configuration.TaintCleanReach

class BaseOnlyCleanerDeduplicationTest {
    @Test
    fun `clearing a mark does not duplicate an implicit Any branch`() {
        val manager = BaseOnlyApManager(
            AnyAccessorUnrollStrategy.AnyAccessorDisabled,
            Cancellation(),
            fieldSensitive = true,
        )
        val base = AccessPathBase.Argument(0)
        val mark = TaintMarkAccessor("mark")
        val fact = manager.createFinalAp(base, ExclusionSet.Empty).prependAccessor(mark)
        val reader = FinalFactReader(fact, manager)
        val initial = EvaluatedCleanAction.initial(reader)
        val rule = object : CommonTaintConfigurationItem {}
        val action = object : CommonTaintAction {}

        val result = TaintCleanActionEvaluator().removeFinalFact(
            initial,
            PositionAccess.Simple(base),
            mark,
            rule,
            action,
            TaintCleanReach.Exact,
        )

        assertEquals(1, result.size)
        assertEquals(fact, result.single().fact?.factAp)
    }
}
