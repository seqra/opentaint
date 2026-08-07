package org.opentaint.dataflow.jvm.ap.ifds.taint

import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.Phase
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.configuration.isTrue
import org.opentaint.dataflow.configuration.jvm.Condition
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.jvm.ap.ifds.CallPositionToJIRValueResolver
import org.opentaint.dataflow.jvm.ap.ifds.CalleePositionToJIRValueResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRMarkAwareConditionRewriter
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.ir.api.jvm.JIRField
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRMethodCallExpr
import org.opentaint.ir.api.jvm.ext.cfg.callExpr

class JIRTaintAnalysisContext(
    override val taintSinkTracker: TaintSinkTracker,
    private val taintConfig: TaintRulesProvider,
    val externalMethodTracker: ExternalMethodTracker? = null,
    val relevantRuleIds: MutableSet<String>,
) : TaintAnalysisContext {
    private lateinit var analysisContext: JIRMethodAnalysisContext

    fun bindAnalysisContext(analysisContext: JIRMethodAnalysisContext) {
        this.analysisContext = analysisContext
    }

    fun reset() {
        taintSinkTracker.reset()
    }

    private fun JIRInst.methodCallExprOrNull(): JIRMethodCallExpr? =
        callExpr as? JIRMethodCallExpr

    fun allRelevantSourceRulesForCallStatement(statement: JIRInst): Iterable<TaintMethodSource> {
        if (analysisContext.phase is Phase.Prescan) return emptyList()
        val method = statement.methodCallExprOrNull()?.method?.method ?: return emptyList()
        return taintConfig.sourceRulesForMethod(method, statement, fact = null, allRelevant = true)
    }

    fun allRelevantCleanRulesForCallStatement(statement: JIRInst): Iterable<TaintCleaner> {
        if (analysisContext.phase is Phase.Prescan) return emptyList()
        val method = statement.methodCallExprOrNull()?.method?.method ?: return emptyList()
        return taintConfig.cleanerRulesForMethod(method, statement, fact = null, allRelevant = true)
    }

    fun sourceRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRMethodCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintMethodSource>> {
        val method = callExpr.method.method
        return prepareCallStatementRules(
            taintConfig.sourceRulesForMethod(method, statement, fact, allRelevant = false),
            TaintMethodSource::condition,
            statement, callExpr, returnValue
        )
    }

    fun sinkRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRMethodCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintMethodSink>> {
        val method = callExpr.method.method
        return prepareCallStatementRules(
            taintConfig.sinkRulesForMethod(method, statement, fact, allRelevant = false),
            TaintMethodSink::condition,
            statement, callExpr, returnValue
        )
    }

    fun cleanRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRMethodCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintCleaner>> {
        val method = callExpr.method.method
        return prepareCallStatementRules(
            taintConfig.cleanerRulesForMethod(method, statement, fact, allRelevant = false),
            TaintCleaner::condition,
            statement, callExpr, returnValue
        )
    }

    fun passRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRMethodCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ): List<RuleWithCondition<TaintPassThrough>> {
        val method = callExpr.method.method
        return prepareCallStatementRules(
            taintConfig.passTroughRulesForMethod(method, statement, fact, allRelevant = false),
            TaintPassThrough::condition,
            statement, callExpr, returnValue
        )
    }

    private inline fun <T: TaintConfigurationItem> prepareCallStatementRules(
        rules: Iterable<T>, cond: T.() -> Condition,
        statement: JIRInst, callExpr: JIRMethodCallExpr, returnValue: JIRImmediate?,
    ): List<RuleWithCondition<T>> {
        val conditionRewriter = JIRMarkAwareConditionRewriter(
            CallPositionToJIRValueResolver(callExpr, returnValue),
            analysisContext, statement
        )

        return rules.mapNotNull {
            val cond = conditionRewriter.rewrite(it.cond())
            if (cond.isFalse) return@mapNotNull null

            RuleWithCondition(it, cond)
        }.handlePhase()
    }

    fun sourceRulesForStaticField(
        field: JIRField,
        statement: JIRInst,
        fact: FinalFactAp?
    ) = taintConfig.sourceRulesForStaticField(field, statement, fact, allRelevant = false).map {
        if (!it.condition.isTrue()) {
            TODO("Field source with complex condition")
        }

        RuleWithCondition(it, RuleConditionRewriter.trueExpr)
    }.handlePhase()

    fun sourceRulesForMethodExit(
        statement: JIRInst,
        fact: FinalFactAp?
    ) = prepareMethodRules(
        taintConfig.exitSourceRulesForMethod(statement.location.method, statement, fact, allRelevant = false),
        TaintMethodExitSource::condition,
        statement
    )

    fun sinkRulesForMethodExit(
        statement: JIRInst,
        fact: FinalFactAp?,
        initialFacts: Set<InitialFactAp>?
    ) = prepareMethodRules(
        taintConfig.sinkRulesForMethodExit(statement.location.method, statement, fact, initialFacts),
        TaintMethodExitSink::condition,
        statement
    )

    fun sinkRulesForMethodEntry(statement: JIRInst, fact: FinalFactAp?) = prepareMethodRules(
        taintConfig.sinkRulesForMethodEntry(statement.location.method, statement, fact),
        TaintMethodEntrySink::condition,
        statement
    )

    fun sourceRulesForMethodEntry(
        statement: JIRInst,
        fact: FinalFactAp?
    ) = prepareMethodRules(
        taintConfig.entryPointRulesForMethod(statement.location.method, statement, fact),
        TaintEntryPointSource::condition,
        statement
    )

    private inline fun <T : TaintConfigurationItem> prepareMethodRules(
        rules: Iterable<T>, cond: T.() -> Condition,
        statement: JIRInst,
    ): List<RuleWithCondition<T>> {
        val method = statement.location.method
        val valueResolver = CalleePositionToJIRValueResolver(method)
        val conditionRewriter = JIRMarkAwareConditionRewriter(
            valueResolver, analysisContext, statement
        )

        return rules.mapNotNull {
            val cond = conditionRewriter.rewrite(it.cond())
            if (cond.isFalse) return@mapNotNull null

            RuleWithCondition(it, cond)
        }.handlePhase()
    }

    private fun <T : TaintConfigurationItem> List<RuleWithCondition<T>>.handlePhase() =
        if (analysisContext.phase !is Phase.Prescan) {
            this
        } else {
            mapNotNullTo(relevantRuleIds) { it.rule.serializedId }
            emptyList()
        }
}
