package org.opentaint.dataflow.jvm.ap.ifds.taint

import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.Phase
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.markset.MarkSetRecorder
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.isTrue
import org.opentaint.dataflow.configuration.jvm.Condition
import org.opentaint.dataflow.configuration.jvm.ContainsMark
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
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
        markSetRecorder = analysisContext.analysisManager.markSetRecorder()
    }

    fun reset() {
        taintSinkTracker.reset()
    }

    /**
     * Non-null only with the mark-set scan on (spec §10); see [recordMarkSet]. Resolved once, by
     * [bindAnalysisContext]: the manager's recorder is fixed, and this is read on every rule query.
     */
    internal var markSetRecorder: MarkSetRecorder? = null
        private set

    private val isMarkSetRecording: Boolean
        get() = markSetRecorder?.active == true && analysisContext.phase is Phase.Prescan

    /** Mark-set debug checks (E2): the full scan is observed; see [observeMarkSet]. */
    private val isMarkSetObserving: Boolean
        get() = markSetRecorder?.observing == true && analysisContext.phase is Phase.FullScan

    /** The rules the full scan would use without the mark-set selection (debug checks only). */
    private val unrestrictedConfig: TaintRulesProvider? = (taintConfig as? SelectedTaintRulesProvider)?.unrestricted

    /**
     * The provider E2 observes the full scan with: [unrestrictedConfig]. Without one, filtered rules
     * would pass E2 vacuously, so the observation is reported as unavailable (an E2 violation).
     */
    private fun observedConfig(): TaintRulesProvider? = unrestrictedConfig ?: run {
        markSetRecorder?.observeUnavailable(
            "the rules provider ${taintConfig::class.qualifiedName} is not a SelectedTaintRulesProvider"
        )
        null
    }

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
        { sourceRulesForMethod(statement.calleeMethod(), statement, fact, allRelevant = false) },
        TaintMethodSource::condition,
        statement, callExpr, returnValue
    )

    fun sinkRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ) = prepareCallStatementRules(
        { sinkRulesForMethod(statement.calleeMethod(), statement, fact, allRelevant = false) },
        TaintMethodSink::condition,
        statement, callExpr, returnValue
    )

    fun cleanRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ) = prepareCallStatementRules(
        { cleanerRulesForMethod(statement.calleeMethod(), statement, fact, allRelevant = false) },
        TaintCleaner::condition,
        statement, callExpr, returnValue
    )

    fun passRulesForCallStatement(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        fact: FinalFactAp?
    ) = prepareCallStatementRules(
        { passTroughRulesForMethod(statement.calleeMethod(), statement, fact, allRelevant = false) },
        TaintPassThrough::condition,
        statement, callExpr, returnValue
    )

    /**
     * Mark-set prescan only (spec §5.2, G4): records the cleaners and pass-throughs of a call on
     * the zero fact, which the prescan otherwise never queries there. The rules are only recorded:
     * nothing is returned and, unlike [handlePhase], the relevant rule ids are left unchanged, so
     * the full scan's rule set stays the baseline's.
     *
     * Only the residual's positive mark literals matter for these kinds, and the rewriter makes
     * literals only from mark atoms, so a rule whose condition has no mark atom is skipped before
     * the rewrite: the recorder would drop its residual anyway. Pass-throughs are looked up once
     * per callee, with no statement (as the alias analysis does), because querying the provider
     * at every call is what made this hook costly; every pass-through provider is
     * statement-independent. Shipped pass-throughs have no mark atom (E8), so the memo is almost
     * always empty.
     */
    fun recordZeroFactCallRules(statement: JIRInst, callExpr: JIRCallExpr, returnValue: JIRImmediate?) {
        if (!isMarkSetRecording) return

        val method = statement.calleeMethod()
        val cleaners = taintConfig.cleanerRulesForMethod(method, statement, fact = null, allRelevant = false)
            .filter { it.condition.hasMarkAtom() }
        if (cleaners.isNotEmpty()) {
            recordMarkSet(
                statement,
                rewriteCallStatementRules(cleaners, TaintCleaner::condition, statement, callExpr, returnValue)
            )
        }

        val passThroughs = markSetPassThroughsWithMarks(method)
        if (passThroughs.isNotEmpty()) {
            recordMarkSet(
                statement,
                rewriteCallStatementRules(passThroughs, TaintPassThrough::condition, statement, callExpr, returnValue)
            )
        }
    }

    private fun markSetPassThroughsWithMarks(method: JIRMethod): List<TaintPassThrough> {
        val memo = analysisContext.analysisManager.markSetPassThroughs
        memo[method]?.let { return it }
        val rules = taintConfig.passTroughRulesForMethod(method, statement = null, fact = null, allRelevant = false)
            .filter { it.condition.hasMarkAtom() }
        return memo.putIfAbsent(method, rules) ?: rules
    }

    private fun Condition.hasMarkAtom(): Boolean = when (this) {
        is CommonCondition.True -> false
        is CommonCondition.Atom -> atom is ContainsMark || atom is ContainsMarkOnAnyField
        is CommonCondition.Not -> arg.hasMarkAtom()
        is CommonCondition.And -> args.any { it.hasMarkAtom() }
        is CommonCondition.Or -> args.any { it.hasMarkAtom() }
    }

    private inline fun <T: TaintConfigurationItem> prepareCallStatementRules(
        rules: TaintRulesProvider.() -> Iterable<T>, cond: T.() -> Condition,
        statement: JIRInst, callExpr: JIRCallExpr, returnValue: JIRImmediate?,
    ): List<RuleWithCondition<T>> {
        if (isMarkSetObserving) {
            observedConfig()?.let { config ->
                observeMarkSet(
                    statement,
                    rewriteCallStatementRules(config.rules(), cond, statement, callExpr, returnValue)
                )
            }
        }

        return rewriteCallStatementRules(taintConfig.rules(), cond, statement, callExpr, returnValue)
            .also { recordMarkSet(statement, it) }
            .handlePhase()
    }

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
    ): List<RuleWithCondition<TaintStaticFieldSource>> {
        if (isMarkSetObserving) {
            observedConfig()?.let { observeMarkSet(statement, staticFieldRules(it, field, statement, fact)) }
        }

        return staticFieldRules(taintConfig, field, statement, fact).also { recordMarkSet(statement, it) }.handlePhase()
    }

    private fun staticFieldRules(
        config: TaintRulesProvider,
        field: JIRField,
        statement: JIRInst,
        fact: FinalFactAp?
    ) = config.sourceRulesForStaticField(field, statement, fact, allRelevant = false).map {
        if (!it.condition.isTrue()) {
            TODO("Field source with complex condition")
        }

        RuleWithCondition(it, RuleConditionRewriter.trueExpr)
    }

    fun sourceRulesForMethodExit(
        statement: JIRInst,
        fact: FinalFactAp?
    ) = prepareMethodRules(
        { exitSourceRulesForMethod(statement.location.method, statement, fact, allRelevant = false) },
        TaintMethodExitSource::condition,
        statement
    )

    fun sinkRulesForMethodExit(
        statement: JIRInst,
        fact: FinalFactAp?,
        initialFacts: Set<InitialFactAp>?
    ) = prepareMethodRules(
        { sinkRulesForMethodExit(statement.location.method, statement, fact, initialFacts) },
        TaintMethodExitSink::condition,
        statement
    )

    fun sinkRulesForMethodEntry(statement: JIRInst, fact: FinalFactAp?) = prepareMethodRules(
        { sinkRulesForMethodEntry(statement.location.method, statement, fact) },
        TaintMethodEntrySink::condition,
        statement
    )

    fun sourceRulesForMethodEntry(
        statement: JIRInst,
        fact: FinalFactAp?
    ) = prepareMethodRules(
        { entryPointRulesForMethod(statement.location.method, statement, fact) },
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
        rules: TaintRulesProvider.() -> Iterable<T>, cond: T.() -> Condition,
        statement: JIRInst,
    ): List<RuleWithCondition<T>> {
        if (isMarkSetObserving) {
            observedConfig()?.let { observeMarkSet(statement, rewriteMethodRules(it.rules(), cond, statement)) }
        }

        return rewriteMethodRules(taintConfig.rules(), cond, statement)
            .also { recordMarkSet(statement, it) }
            .handlePhase()
    }

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
