package org.opentaint.semgrep.pattern

import org.opentaint.dataflow.configuration.jvm.serialized.UserDefinedRuleInfo

data class UserRuleFromSemgrepInfo(
    val ruleId: String,
    override val relevantTaintMarks: Set<String>
) : UserDefinedRuleInfo
