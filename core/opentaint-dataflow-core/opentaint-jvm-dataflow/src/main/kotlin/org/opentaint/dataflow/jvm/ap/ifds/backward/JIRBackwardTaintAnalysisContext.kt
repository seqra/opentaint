package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.Condition
import org.opentaint.dataflow.configuration.jvm.ContainsMark
import org.opentaint.dataflow.configuration.jvm.JirCondition
import org.opentaint.dataflow.configuration.jvm.PositionAccessor
import org.opentaint.dataflow.configuration.jvm.PositionWithAccess
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintSinkMeta
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.dataflow.configuration.mkOr
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.jvm.ap.ifds.CallPositionToJIRValueResolver
import org.opentaint.dataflow.jvm.ap.ifds.CalleePositionToJIRValueResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRMarkAwareConditionRewriter
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.taint.ContainsMarkOnAnyField
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintRuleContext
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveBaseAp
import org.opentaint.dataflow.taint.RuleConditionRewriter.Companion.trueExpr
import org.opentaint.dataflow.taint.RuleConditionRewriter.ExprOrConstant
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr
import org.opentaint.ir.api.jvm.JIRField
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.ext.cfg.callExpr

internal class JIRBackwardTaintAnalysisContext(
    private val forward: JIRTaintAnalysisContext,
    private val rules: TaintRulesProvider,
) : JIRTaintRuleContext by forward {
    private lateinit var analysisContext: JIRMethodAnalysisContext

    override fun bindAnalysisContext(analysisContext: JIRMethodAnalysisContext) {
        this.analysisContext = analysisContext
        forward.bindAnalysisContext(analysisContext)
    }

    override fun allRelevantCleanRulesForCallStatement(statement: JIRInst): Iterable<TaintCleaner> {
        val cleaners = forward.allRelevantCleanRulesForCallStatement(statement)
        val callExpr = statement.callExpr ?: return cleaners
        val returnValue = (statement as? JIRAssignInst)?.lhv as? JIRImmediate
        val rewriter = JIRMarkAwareConditionRewriter(
            CallPositionToJIRValueResolver(callExpr, returnValue), analysisContext, statement
        )
        return cleaners.filter {
            val condition = rewriter.rewrite(it.condition)
            condition.isFalse || conditionMarks(it.condition, condition) == null
        }
    }

    override fun sourceRulesForCallStatement(
        statement: JIRInst, callExpr: JIRCallExpr, returnValue: JIRImmediate?, fact: FinalFactAp?
    ): List<RuleWithCondition<TaintMethodSource>> =
        conditionalSources(forward.sourceRulesForCallStatement(statement, callExpr, returnValue, fact), dropResult = true) { source, marks ->
            source.copy(condition = source.produced(), actionsAfter = marks)
        } + seedingSources(forward.sinkRulesForCallStatement(statement, callExpr, returnValue, fact), dropResult = true) { sink, marks ->
            TaintMethodSource(sink.method, mkTrue(), marks, sink.info, sink.serializedId)
        }

    override fun sinkRulesForCallStatement(
        statement: JIRInst, callExpr: JIRCallExpr, returnValue: JIRImmediate?, fact: FinalFactAp?
    ): List<RuleWithCondition<TaintMethodSink>> =
        sourceSinks(forward.sourceRulesForCallStatement(statement, callExpr, returnValue, fact)) { source, id, meta ->
            TaintMethodSink(source.method, source.produced(), emptyList(), id, meta, source.info, source.serializedId)
        } + unconditional(forward.sinkRulesForCallStatement(statement, callExpr, returnValue, fact), TaintConfigurationSink::condition) {
            it.copy(condition = mkTrue(), trackFactsReachAnalysisEnd = emptyList())
        }

    override fun cleanRulesForCallStatement(
        statement: JIRInst, callExpr: JIRCallExpr, returnValue: JIRImmediate?, fact: FinalFactAp?
    ): List<RuleWithCondition<TaintCleaner>> =
        unconditional(forward.cleanRulesForCallStatement(statement, callExpr, returnValue, fact), TaintCleaner::condition) { it }

    override fun sourceRulesForStaticField(
        field: JIRField, statement: JIRInst, fact: FinalFactAp?
    ): List<RuleWithCondition<TaintStaticFieldSource>> =
        conditionalSources(staticFieldSources(field, statement, fact), dropResult = true) { source, marks ->
            source.copy(condition = source.produced(), actionsAfter = marks)
        }

    fun sinkRulesForStaticField(field: JIRField, statement: JIRInst): List<RuleWithCondition<TaintMethodSink>> =
        sourceSinks(staticFieldSources(field, statement, fact = null)) { source, id, meta ->
            TaintMethodSink(statement.location.method, source.produced(), emptyList(), id, meta, source.info, source.serializedId)
        }

    override fun sourceRulesForMethodExit(statement: JIRInst, fact: FinalFactAp?): List<RuleWithCondition<TaintMethodExitSource>> =
        conditionalSources(forward.sourceRulesForMethodExit(statement, fact), dropResult = false) { source, marks ->
            source.copy(condition = source.produced(), actionsAfter = marks)
        } + seedingSources(exitSinks(statement, fact), dropResult = false) { sink, marks ->
            TaintMethodExitSource(sink.method, mkTrue(), marks, sink.info, sink.serializedId)
        }

    override fun sinkRulesForMethodExit(
        statement: JIRInst, fact: FinalFactAp?, initialFacts: Set<InitialFactAp>?
    ): List<RuleWithCondition<TaintMethodExitSink>> =
        sourceSinks(forward.sourceRulesForMethodExit(statement, fact)) { source, id, meta ->
            TaintMethodExitSink(source.method, source.produced(), emptyList(), id, meta, source.info, source.serializedId)
        } + unconditional(exitSinks(statement, fact), TaintConfigurationSink::condition) {
            it.copy(condition = mkTrue(), trackFactsReachAnalysisEnd = emptyList())
        }

    override fun sinkRulesForMethodEntry(statement: JIRInst, fact: FinalFactAp?): List<RuleWithCondition<TaintMethodEntrySink>> =
        sourceSinks(forward.sourceRulesForMethodEntry(statement, fact)) { source, id, meta ->
            TaintMethodEntrySink(source.method, source.produced(), emptyList(), id, meta, source.info, source.serializedId)
        } + unconditional(forward.sinkRulesForMethodEntry(statement, fact), TaintConfigurationSink::condition) {
            it.copy(condition = mkTrue(), trackFactsReachAnalysisEnd = emptyList())
        }

    override fun sourceRulesForMethodEntry(statement: JIRInst, fact: FinalFactAp?): List<RuleWithCondition<TaintEntryPointSource>> =
        conditionalSources(forward.sourceRulesForMethodEntry(statement, fact), dropResult = true) { source, marks ->
            source.copy(condition = source.produced(), actionsAfter = marks)
        } + seedingSources(forward.sinkRulesForMethodEntry(statement, fact), dropResult = true) { sink, marks ->
            TaintEntryPointSource(sink.method, mkTrue(), marks, sink.info, sink.serializedId)
        }

    private fun exitSinks(statement: JIRInst, fact: FinalFactAp?) =
        forward.sinkRulesForMethodExit(statement, fact, initialFacts = emptySet())

    private fun staticFieldSources(
        field: JIRField, statement: JIRInst, fact: FinalFactAp?
    ): List<RuleWithCondition<TaintStaticFieldSource>> {
        val rewriter = JIRMarkAwareConditionRewriter(
            CalleePositionToJIRValueResolver(statement.location.method), analysisContext, statement
        )
        return rules.sourceRulesForStaticField(field, statement, fact).mapNotNull { rule ->
            val condition = rewriter.rewrite(rule.condition)
            if (condition.isFalse) null else RuleWithCondition(rule, condition)
        }
    }

    private inline fun <S : TaintConfigurationSource, T> sourceSinks(
        sources: List<RuleWithCondition<S>>,
        create: (S, String, TaintSinkMeta) -> T,
    ): List<RuleWithCondition<T>> = sources.mapNotNull { (source, condition) ->
        if (source.actionsAfter.isEmpty() || conditionMarks(source.condition, condition) != null) return@mapNotNull null
        val (id, meta) = rules.sinkMetaForSource(source) ?: syntheticMeta(source)
        RuleWithCondition(create(source, id, meta), source.producedExpr())
    }

    private inline fun <S : TaintConfigurationSource> conditionalSources(
        sources: List<RuleWithCondition<S>>,
        dropResult: Boolean,
        create: (S, List<AssignMark>) -> S,
    ): List<RuleWithCondition<S>> = sources.mapNotNull { (source, condition) ->
        val marks = conditionMarks(source.condition, condition)?.demanded(dropResult)
        if (marks.isNullOrEmpty() || source.actionsAfter.isEmpty()) return@mapNotNull null
        RuleWithCondition(create(source, marks), source.producedExpr())
    }

    private inline fun <K : TaintConfigurationSink, S> seedingSources(
        sinks: List<RuleWithCondition<K>>,
        dropResult: Boolean,
        create: (K, List<AssignMark>) -> S,
    ): List<RuleWithCondition<S>> = sinks.mapNotNull { (sink, condition) ->
        val marks = conditionMarks(sink.condition, condition)?.demanded(dropResult)
        if (marks.isNullOrEmpty()) return@mapNotNull null
        RuleWithCondition(create(sink, marks), trueExpr)
    }

    private inline fun <R> unconditional(
        rules: List<RuleWithCondition<R>>,
        ruleCondition: (R) -> Condition,
        copy: (R) -> R,
    ): List<RuleWithCondition<R>> = rules.mapNotNull { (rule, condition) ->
        if (conditionMarks(ruleCondition(rule), condition) != null) return@mapNotNull null
        RuleWithCondition(copy(rule), trueExpr)
    }

    private fun List<AssignMark>.demanded(dropResult: Boolean): List<AssignMark> =
        filter { !dropResult || it.position.resolveBaseAp() != AccessPathBase.Return }.distinct()

    private fun syntheticMeta(source: TaintConfigurationSource): Pair<String, TaintSinkMeta> {
        val id = source.serializedId ?: source.actionsAfter.joinToString(",") { it.mark.name }
        return id to TaintSinkMeta(message = "", CommonTaintConfigurationSinkMeta.Severity.Warning, cwe = null)
    }

    companion object {
        private fun conditionMarks(condition: Condition, prepared: ExprOrConstant): List<AssignMark>? {
            if (prepared.isTrue) return null
            val literals = hashSetOf<TaintMarkAwareConditionExpr.Literal>()
            prepared.expr.collectPositiveLiterals(literals)
            if (literals.isEmpty()) return null
            return condition.positiveMarkAtoms().filter { it.literal() in literals }.flatMap { it.markActions() }
        }

        private fun TaintMarkAwareConditionExpr.collectPositiveLiterals(literals: MutableSet<TaintMarkAwareConditionExpr.Literal>) {
            when (this) {
                is TaintMarkAwareConditionExpr.Literal -> if (!negated) literals += this
                is TaintMarkAwareConditionExpr.And -> args.forEach { it.collectPositiveLiterals(literals) }
                is TaintMarkAwareConditionExpr.Or -> args.forEach { it.collectPositiveLiterals(literals) }
            }
        }

        private fun TaintConfigurationSource.produced(): Condition =
            mkOr(actionsAfter.map { CommonCondition.Atom(it.contained()) })

        private fun TaintConfigurationSource.producedExpr(): ExprOrConstant {
            val literals = actionsAfter.mapNotNull { it.contained().literal() }.distinct()
            return ExprOrConstant(literals.singleOrNull() ?: TaintMarkAwareConditionExpr.Or(literals.toTypedArray()))
        }

        private fun AssignMark.contained(): JirCondition {
            val position = position
            if (position is PositionWithAccess && position.access == PositionAccessor.AnyFieldAccessor) {
                return ContainsMarkOnAnyField(position.base, mark)
            }
            return ContainsMark(position, mark)
        }

        private fun JirCondition.literal(): TaintMarkAwareConditionExpr.Literal? = when (this) {
            is ContainsMark -> TaintMarkAwareConditionExpr.ContainsMarkLiteral(
                position.resolveAp(), TaintMarkAccessor(mark.name), negated = false
            )
            is ContainsMarkOnAnyField -> TaintMarkAwareConditionExpr.ContainsMarkOnAnyAccessorLiteral(
                position.resolveAp(), TaintMarkAccessor(mark.name), negated = false
            )
            else -> null
        }

        private fun JirCondition.markActions(): List<AssignMark> = when (this) {
            is ContainsMark -> listOf(AssignMark(mark, position))
            is ContainsMarkOnAnyField -> listOf(
                AssignMark(mark, position),
                AssignMark(mark, PositionWithAccess(position, PositionAccessor.AnyFieldAccessor)),
            )
            else -> emptyList()
        }

        private fun Condition.positiveMarkAtoms(): List<JirCondition> = when (this) {
            is CommonCondition.Atom -> listOf(atom)
            is CommonCondition.And -> args.flatMap { it.positiveMarkAtoms() }
            is CommonCondition.Or -> args.flatMap { it.positiveMarkAtoms() }
            is CommonCondition.True, is CommonCondition.Not -> emptyList()
        }

        fun Condition.positiveMarks(): List<AssignMark> = positiveMarkAtoms().flatMap { it.markActions() }
    }
}
