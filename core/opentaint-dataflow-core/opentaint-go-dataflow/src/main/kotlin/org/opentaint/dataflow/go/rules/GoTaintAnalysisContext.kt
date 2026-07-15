package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoFieldSignature
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.GoGlobalFieldSignature
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRValue

class GoTaintAnalysisContext(
    override val taintSinkTracker: TaintSinkTracker,
    private val taintConfig: GoTaintRulesProvider,
    val externalMethodTracker: ExternalMethodTracker? = null,
) : TaintAnalysisContext {
    fun allRelevantSourceRulesForCallStatement(
        signature: GoFunctionSignature,
        statement: GoIRInst,
        callExpr: GoCallExpr,
        returnValue: GoIRValue?
    ) = prepareCallStatementRules(
        taintConfig.sourceRulesForCall(signature, allRelevant = true),
        TaintRule.Source::condition,
        statement, callExpr, returnValue
    )

    fun allRelevantCleanRulesForCallStatement(
        signature: GoFunctionSignature,
        statement: GoIRInst,
        callExpr: GoCallExpr,
        returnValue: GoIRValue?
    ) = prepareCallStatementRules(
        taintConfig.cleanerRulesForCall(signature, allRelevant = true),
        TaintRule.Cleaner::condition,
        statement, callExpr, returnValue
    )

    fun sourceRulesForCallStatement(
        signature: GoFunctionSignature,
        statement: GoIRInst,
        callExpr: GoCallExpr,
        returnValue: GoIRValue?
    ) = prepareCallStatementRules(
        taintConfig.sourceRulesForCall(signature),
        TaintRule.Source::condition,
        statement, callExpr, returnValue
    )

    fun sinkRulesForCallStatement(
        signature: GoFunctionSignature,
        statement: GoIRInst,
        callExpr: GoCallExpr,
        returnValue: GoIRValue?
    ) = prepareCallStatementRules(
        taintConfig.sinkRulesForCall(signature),
        TaintRule.Sink::condition,
        statement, callExpr, returnValue
    )

    private inline fun <T> prepareCallStatementRules(
        rules: List<T>,
        cond: T.() -> CommonCondition<GoRuleCondition>,
        statement: GoIRInst,
        callExpr: GoCallExpr,
        returnValue: GoIRValue?
    ): List<RuleWithCondition<T>> {
        val rewriter = GoRuleConditionRewriter(callExpr, statement, returnValue)
        return rules.mapNotNull {
            val cond = rewriter.rewrite(it.cond())
            if (cond.isFalse) return@mapNotNull null

            RuleWithCondition(it, cond)
        }
    }

    fun passRulesForCallStatement(signature: GoFunctionSignature): List<TaintRule.PassThrough> =
        taintConfig.passThroughRulesForCall(signature)

    fun sourceRulesForFieldRead(fieldName: GoFieldSignature): List<TaintRule.FieldReadSource> =
        taintConfig.sourceRulesForFieldRead(fieldName)

    fun sourceRulesForGlobal(globalName: GoGlobalFieldSignature): List<TaintRule.GlobalReadSource> =
        taintConfig.sourceRulesForGlobal(globalName)
}
