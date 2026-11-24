package org.opentaint.semgrep.pattern

import java.io.File
import kotlin.test.Test
import kotlin.test.assertEquals

class SemgrepRuleUtilsTest {
    @Test
    fun `semgrep-style id joins the rule set directories and the rule id with dots`() {
        val ruleId = SemgrepRuleUtils.getRuleId(listOf("java", "security", "xss.yaml").joinToString(File.separator), "xss")
        assertEquals("java.security.xss", SemgrepRuleUtils.getSemgrepStyleRuleId(ruleId))
    }

    @Test
    fun `semgrep-style id of a top-level rule set is the rule id`() {
        assertEquals("xss", SemgrepRuleUtils.getSemgrepStyleRuleId("xss.yaml:xss"))
    }

    @Test
    fun `id without a rule set stays as is`() {
        assertEquals("xss", SemgrepRuleUtils.getSemgrepStyleRuleId("xss"))
    }
}
