package org.opentaint.semgrep.pattern.conversion.taint

import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.conversion.LanguageTypeOps

class RuleConversionCtx(
    val ruleId: String,
    val modeModifier: String?,
    val meta: SinkMetaData,
    val trace: SemgrepRuleLoadStepTrace,
    val typeOps: LanguageTypeOps,
)
