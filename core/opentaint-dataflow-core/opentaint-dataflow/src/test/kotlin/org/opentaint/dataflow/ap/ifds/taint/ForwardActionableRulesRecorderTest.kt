package org.opentaint.dataflow.ap.ifds.taint

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotSame
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation

class ForwardActionableRulesRecorderTest {
    private val statement = object : CommonInst {
        override val location: CommonInstLocation
            get() = error("Unused by the recorder")
    }
    private val rule = object : CommonTaintConfigurationItem {}
    private val action = object : CommonTaintAction {}

    @Test
    fun `record is idempotent and snapshot is detached`() {
        val recorder = ForwardActionableRulesRecorder()

        recorder.record(statement, rule, action)
        recorder.record(statement, rule, action)

        val first = recorder.snapshot()
        assertEquals(setOf(action), first.getValue(statement).getValue(rule))

        recorder.reset()
        val second = recorder.snapshot()
        assertEquals(emptyMap(), second)
        assertNotSame(first, second)
        assertEquals(setOf(action), first.getValue(statement).getValue(rule))
    }
}
