package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.Phase
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoFieldSignature
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.GoGlobalFieldSignature
import org.opentaint.dataflow.go.analysis.GoMethodAnalysisContext
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRValue

class GoTaintAnalysisContext(
    override val taintSinkTracker: TaintSinkTracker,
    private val taintConfig: GoTaintRulesProvider,
    val externalMethodTracker: ExternalMethodTracker? = null,
    val relevantRuleIds: MutableSet<String> = mutableSetOf(),
) : TaintAnalysisContext {
    private var analysisContext: GoMethodAnalysisContext? = null
    private val phase: Phase get() = analysisContext?.phase ?: Phase.FullScan

    fun bindAnalysisContext(analysisContext: GoMethodAnalysisContext) {
        this.analysisContext = analysisContext
    }

    fun allRelevantSourceRulesForCallStatement(
        signature: GoFunctionSignature,
        statement: GoIRInst,
        callExpr: GoCallExpr,
        returnValue: GoIRValue?,
    ): List<RuleWithCondition<TaintRule.Source>> {
        if (phase is Phase.Prescan) return emptyList()
        return prepareCallStatementRules(
            taintConfig.sourceRulesForCall(signature, allRelevant = true),
            TaintRule.Source::condition,
            statement, callExpr, returnValue,
        )
    }

    fun allRelevantCleanRulesForCallStatement(
        signature: GoFunctionSignature,
        statement: GoIRInst,
        callExpr: GoCallExpr,
        returnValue: GoIRValue?,
    ): List<RuleWithCondition<TaintRule.Cleaner>> = prepareCallStatementRules(
        taintConfig.cleanerRulesForCall(signature, allRelevant = true),
        TaintRule.Cleaner::condition,
        statement, callExpr, returnValue,
    )

    fun sourceRulesForCallStatement(
        signature: GoFunctionSignature,
        statement: GoIRInst,
        callExpr: GoCallExpr,
        returnValue: GoIRValue?,
    ) = prepareCallStatementRules(
        taintConfig.sourceRulesForCall(signature),
        TaintRule.Source::condition,
        statement, callExpr, returnValue,
    )

    fun sinkRulesForCallStatement(
        signature: GoFunctionSignature,
        statement: GoIRInst,
        callExpr: GoCallExpr,
        returnValue: GoIRValue?,
    ) = prepareCallStatementRules(
        taintConfig.sinkRulesForCall(signature),
        TaintRule.Sink::condition,
        statement, callExpr, returnValue,
    )

    private inline fun <T : TaintRule> prepareCallStatementRules(
        rules: List<T>,
        cond: T.() -> CommonCondition<GoRuleCondition>,
        statement: GoIRInst,
        callExpr: GoCallExpr,
        returnValue: GoIRValue?,
    ): List<RuleWithCondition<T>> {
        val rewriter = GoRuleConditionRewriter(callExpr, statement, returnValue)
        return rules.mapNotNull {
            val condition = rewriter.rewrite(it.cond())
            if (condition.isFalse) return@mapNotNull null
            RuleWithCondition(it, condition)
        }.handleConditionalPhase()
    }

    fun passRulesForCallStatement(signature: GoFunctionSignature): List<TaintRule.PassThrough> =
        taintConfig.passThroughRulesForCall(signature).handlePhase()

    fun sourceRulesForFieldRead(fieldName: GoFieldSignature): List<TaintRule.FieldReadSource> =
        taintConfig.sourceRulesForFieldRead(fieldName).handlePhase()

    fun sourceRulesForGlobal(globalName: GoGlobalFieldSignature): List<TaintRule.GlobalReadSource> =
        taintConfig.sourceRulesForGlobal(globalName).handlePhase()

    private fun <T : TaintRule> List<T>.handlePhase(): List<T> =
        if (phase !is Phase.Prescan) {
            this
        } else {
            mapNotNullTo(relevantRuleIds) { it.serializedId }
            emptyList()
        }

    private fun <T : TaintRule> List<RuleWithCondition<T>>.handleConditionalPhase(): List<RuleWithCondition<T>> =
        if (phase !is Phase.Prescan) {
            this
        } else {
            mapNotNullTo(relevantRuleIds) { it.rule.serializedId }
            emptyList()
        }
}
