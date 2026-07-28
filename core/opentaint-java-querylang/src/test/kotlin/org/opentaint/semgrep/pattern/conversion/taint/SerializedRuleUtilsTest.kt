package org.opentaint.semgrep.pattern.conversion.taint

import org.opentaint.dataflow.configuration.TaintCleanReach
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.semgrep.pattern.Mark
import kotlin.test.Test
import kotlin.test.assertEquals

class SerializedRuleUtilsTest {
    @Test
    fun `generated state cleanup reaches the AnyField fact alternative`() {
        val mark = Mark.RuleUniqueMarkPrefix(
            ruleId = "rule",
            modeModifier = null,
            idx = 0,
        ).artificialState("state")

        val cleanup = mark.mkCleanMark(PositionBase.Result.base())

        assertEquals(TaintCleanReach.ExactAndAnyField, cleanup.reach)
    }
}
