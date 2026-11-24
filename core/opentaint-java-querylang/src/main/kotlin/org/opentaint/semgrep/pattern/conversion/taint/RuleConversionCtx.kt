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
    val sinkRuleId: String = ruleId,
) {
    private var nextSerializedItemIndex: Int = 0

    fun nextSerializedItemId(type: String): String =
        "$ruleId:$type:${nextSerializedItemIndex++}"

    /**
     * Namespaces the marks and serialized items of one join item under [itemId];
     * its sinks still report the join's own rule id.
     */
    fun joinItemCtx(itemId: String): RuleConversionCtx =
        RuleConversionCtx("$ruleId#$itemId", modeModifier, meta, trace, typeOps, sinkRuleId)
}
