package org.opentaint.dataflow.jvm.ap.ifds.taint

import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.Phase
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.markset.MarkSetRecorder
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
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
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

    /** Non-null only with the mark-set scan on (spec §10); see [recordMarkSet]. */
    internal val markSetRecorder: MarkSetRecorder?
        get() = analysisContext.analysisManager.markSetRecorder()

    private val isMarkSetRecording: Boolean
        get() = analysisContext.phase is Phase.Prescan && markSetRecorder?.active == true

    private fun JIRInst.callExpr(): JIRCallExpr = callExpr ?: error("Non-call statement")
    private fun JIRCallExpr.calleeMethod(): JIRMethod = method.method
    private fun JIRInst.calleeMethod(): JIRMethod = callExpr().calleeMethod()

    fun allRelevantSourceRulesForCallStatement(statement: JIRInst): Iterable<TaintMethodSource> {
        if (analysisContext.phase is Phase.Prescan) return emptyList()
        return taintConfig.sourceRulesForMethod(statement.calleeMethod(), statement, fact = null, allRelevant = true)
    }

    fun allRelevantCleanRulesForCallStatement(statement: JIRInst): Iterable<TaintCleaner> {
        if (analysisContext.phase is Phase.Prescan) return emptyList()
        return taintConfig.cleanerRulesForMethod(statement.calleeMethod(), statement, fact = null, allRelevant = true)
    }

    fun sourceRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ) = prepareCallStatementRules(
        taintConfig.sourceRulesForMethod(statement.calleeMethod(), statement, fact, allRelevant = false),
        TaintMethodSource::condition,
        statement, callExpr, returnValue
    )

    fun sinkRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ) = prepareCallStatementRules(
        taintConfig.sinkRulesForMethod(statement.calleeMethod(), statement, fact, allRelevant = false),
        TaintMethodSink::condition,
        statement, callExpr, returnValue
    )

    fun cleanRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ) = prepareCallStatementRules(
        taintConfig.cleanerRulesForMethod(statement.calleeMethod(), statement, fact, allRelevant = false),
        TaintCleaner::condition,
        statement, callExpr, returnValue
    )

    fun passRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ) = prepareCallStatementRules(
        taintConfig.passTroughRulesForMethod(statement.calleeMethod(), statement, fact, allRelevant = false),
        TaintPassThrough::condition,
        statement, callExpr, returnValue
    )

    /**
     * Mark-set prescan only (spec §5.2, G4): records the cleaners and pass-throughs of a call on
     * the zero fact, which the prescan otherwise never queries there. The rules are only recorded:
     * nothing is returned and, unlike [handlePhase], the relevant rule ids are left unchanged, so
     * the full scan's rule set stays the baseline's.
     */
    fun recordZeroFactCallRules(statement: JIRInst, callExpr: JIRCallExpr, returnValue: JIRImmediate?) {
        if (!isMarkSetRecording) return

        val method = statement.calleeMethod()
        recordMarkSet(
            statement,
            rewriteCallStatementRules(
                taintConfig.cleanerRulesForMethod(method, statement, fact = null, allRelevant = false),
                TaintCleaner::condition, statement, callExpr, returnValue
            )
        )
        recordMarkSet(
            statement,
            rewriteCallStatementRules(
                taintConfig.passTroughRulesForMethod(method, statement, fact = null, allRelevant = false),
                TaintPassThrough::condition, statement, callExpr, returnValue
            )
        )
    }

    private inline fun <T: TaintConfigurationItem> prepareCallStatementRules(
        rules: Iterable<T>, cond: T.() -> Condition,
        statement: JIRInst, callExpr: JIRCallExpr, returnValue: JIRImmediate?,
    ): List<RuleWithCondition<T>> =
        rewriteCallStatementRules(rules, cond, statement, callExpr, returnValue)
            .also { recordMarkSet(statement, it) }
            .handlePhase()

    private inline fun <T: TaintConfigurationItem> rewriteCallStatementRules(
        rules: Iterable<T>, cond: T.() -> Condition,
        statement: JIRInst, callExpr: JIRCallExpr, returnValue: JIRImmediate?,
    ): List<RuleWithCondition<T>> {
        val conditionRewriter = JIRMarkAwareConditionRewriter(
            CallPositionToJIRValueResolver(callExpr, returnValue),
            analysisContext, statement
        )

        return rules.mapNotNull {
            val cond = conditionRewriter.rewrite(it.cond())
            if (cond.isFalse) return@mapNotNull null

            RuleWithCondition(it, cond)
        }
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
    }.also { recordMarkSet(statement, it) }.handlePhase()

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

    /**
     * Mark-set prescan only (spec §5.2, G6): records the exit sources and sinks at a throw on the
     * zero fact; the prescan otherwise queries exit rules at returns only. The rules are only
     * recorded: nothing is returned and the relevant rule ids are left unchanged.
     */
    fun recordZeroFactThrowRules(statement: JIRInst) {
        if (!isMarkSetRecording) return

        val method = statement.location.method
        recordMarkSet(
            statement,
            rewriteMethodRules(
                taintConfig.exitSourceRulesForMethod(method, statement, fact = null, allRelevant = false),
                TaintMethodExitSource::condition, statement
            )
        )
        recordMarkSet(
            statement,
            rewriteMethodRules(
                taintConfig.sinkRulesForMethodExit(method, statement, fact = null, initialFacts = null),
                TaintMethodExitSink::condition, statement
            )
        )
    }

    private inline fun <T : TaintConfigurationItem> prepareMethodRules(
        rules: Iterable<T>, cond: T.() -> Condition,
        statement: JIRInst,
    ): List<RuleWithCondition<T>> =
        rewriteMethodRules(rules, cond, statement)
            .also { recordMarkSet(statement, it) }
            .handlePhase()

    private inline fun <T : TaintConfigurationItem> rewriteMethodRules(
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
        }
    }

    private fun <T : TaintConfigurationItem> List<RuleWithCondition<T>>.handlePhase(): List<RuleWithCondition<T>> {
        if (analysisContext.phase !is Phase.Prescan) return this

        mapNotNullTo(relevantRuleIds) { it.rule.serializedId }

        return filter { it.rule is TaintPassThrough }
    }
}
