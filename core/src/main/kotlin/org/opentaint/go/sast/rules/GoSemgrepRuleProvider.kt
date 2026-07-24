package org.opentaint.go.sast.rules

import org.opentaint.common.sast.rules.SemgrepRuleProvider
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.go.GoFieldSignature
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.GoGlobalFieldSignature
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
import org.opentaint.dataflow.go.rules.TaintRule
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep

class GoSemgrepRuleProvider(
    rules: List<TaintRuleFromSemgrep<GoSerializedItem>>,
    private val base: GoTaintConfiguration,
) : SemgrepRuleProvider<GoSerializedItem, TaintRule>(rules), GoTaintRulesProvider {
    override fun GoSerializedItem.ruleItemId(): String? = id
    override fun TaintRule.resolvedRuleId(): String? = serializedId

    override fun selectRules(ruleIds: Set<String>) = selectRelevantSemgrepRules(ruleIds)

    override fun sourceRulesForGlobal(signature: GoGlobalFieldSignature) =
        base.sourceRulesForGlobal(signature).select().toList()

    override fun sourceRulesForFieldRead(signature: GoFieldSignature) =
        base.sourceRulesForFieldRead(signature).select().toList()

    override fun sourceRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean) =
        base.sourceRulesForCall(signature, allRelevant).select().toList()

    override fun sinkRulesForCall(signature: GoFunctionSignature) =
        base.sinkRulesForCall(signature).select().toList()

    override fun passThroughRulesForCall(signature: GoFunctionSignature) =
        base.passThroughRulesForCall(signature).select().toList()

    override fun cleanerRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean) =
        base.cleanerRulesForCall(signature, allRelevant).select().toList()
}
