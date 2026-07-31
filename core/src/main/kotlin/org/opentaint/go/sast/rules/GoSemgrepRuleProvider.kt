package org.opentaint.go.sast.rules

import org.opentaint.common.sast.rules.SemgrepRuleProvider
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.go.GoFieldSignature
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.GoGlobalFieldSignature
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
import org.opentaint.dataflow.go.rules.TaintRule
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep

class GoSemgrepRuleProvider(
    rules: List<TaintRuleFromSemgrep<GoSerializedItem>>,
    private val base: GoTaintConfiguration,
) : SemgrepRuleProvider<GoSerializedItem, TaintRule>(rules), GoTaintRulesProvider {
    override fun GoSerializedItem.ruleItemId(): String? = serializedId
    override fun TaintRule.resolvedRuleId(): String? = serializedId

    override fun selectRules(ruleIds: Set<String>) = selectRelevantSemgrepRules(ruleIds)

    override fun sourceRulesForGlobal(signature: GoGlobalFieldSignature, statement: GoIRInst) =
        base.sourceRulesForGlobal(signature, statement).select(allRelevant = false).toList()

    override fun sourceRulesForFieldRead(signature: GoFieldSignature, statement: GoIRInst) =
        base.sourceRulesForFieldRead(signature, statement).select(allRelevant = false).toList()

    override fun sourceRulesForCall(signature: GoFunctionSignature, statement: GoIRInst, allRelevant: Boolean) =
        base.sourceRulesForCall(signature, statement, allRelevant).select(allRelevant).toList()

    override fun sinkRulesForCall(signature: GoFunctionSignature, statement: GoIRInst) =
        base.sinkRulesForCall(signature, statement).select(allRelevant = false).toList()

    override fun passThroughRulesForCall(signature: GoFunctionSignature, statement: GoIRInst) =
        base.passThroughRulesForCall(signature, statement)

    override fun cleanerRulesForCall(signature: GoFunctionSignature, statement: GoIRInst, allRelevant: Boolean) =
        base.cleanerRulesForCall(signature, statement, allRelevant)
}
