package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.isFalse
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
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.configuration.jvm.TaintSinkMeta
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.dataflow.configuration.mkAnd
import org.opentaint.dataflow.configuration.mkFalse
import org.opentaint.dataflow.configuration.mkOr
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.configuration.simplify
import org.opentaint.dataflow.jvm.ap.ifds.taint.ContainsMarkOnAnyField
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveBaseAp
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.JIRField
import java.util.concurrent.ConcurrentHashMap

class JIRBackwardTaintRulesProvider(private val base: TaintRulesProvider) : TaintRulesProvider {
    private enum class Derivation { SOURCE_SINKS, SINK_SOURCES, CONDITIONAL_SOURCES, RESIDUAL_SINKS, CLEANERS }

    private val cache = ConcurrentHashMap<Pair<Derivation, Any>, List<Any>>()

    override fun entryPointRulesForMethod(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintEntryPointSource> =
        base.sinkRulesForMethodEntry(method, statement, fact, allRelevant).derived(Derivation.SINK_SOURCES) { sink ->
            sinkSource(sink, dropResult = true) { c, a -> TaintEntryPointSource(sink.method, c, a, sink.info, sink.serializedId) }
        } + base.entryPointRulesForMethod(method, statement, fact, allRelevant).derived(Derivation.CONDITIONAL_SOURCES) {
            conditionalSource(it, dropResult = true) { c, a -> it.copy(condition = c, actionsAfter = a) }
        }

    override fun sourceRulesForMethod(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintMethodSource> {
        val sources = base.sourceRulesForMethod(method, statement, fact, allRelevant)
        if (allRelevant) return sources

        return base.sinkRulesForMethod(method, statement, fact, allRelevant).derived(Derivation.SINK_SOURCES) { sink ->
            sinkSource(sink, dropResult = true) { c, a -> TaintMethodSource(sink.method, c, a, sink.info, sink.serializedId) }
        } + sources.derived(Derivation.CONDITIONAL_SOURCES) {
            conditionalSource(it, dropResult = true) { c, a -> it.copy(condition = c, actionsAfter = a) }
        }
    }

    override fun exitSourceRulesForMethod(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintMethodExitSource> {
        val sinks = base.sinkRulesForMethodExit(method, statement, fact, initialFacts = emptySet(), allRelevant)
        return sinks.derived(Derivation.SINK_SOURCES) { sink ->
            sinkSource(sink, dropResult = false) { c, a -> TaintMethodExitSource(sink.method, c, a, sink.info, sink.serializedId) }
        } + base.exitSourceRulesForMethod(method, statement, fact, allRelevant).derived(Derivation.CONDITIONAL_SOURCES) {
            conditionalSource(it, dropResult = false) { c, a -> it.copy(condition = c, actionsAfter = a) }
        }
    }

    override fun sinkRulesForMethod(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintMethodSink> =
        base.sourceRulesForMethod(method, statement, fact, allRelevant).derived(Derivation.SOURCE_SINKS) { source ->
            sourceSink(source) { c, id, meta ->
                TaintMethodSink(source.method, c, emptyList(), id, meta, source.info, source.serializedId)
            }
        } + base.sinkRulesForMethod(method, statement, fact, allRelevant).derived(Derivation.RESIDUAL_SINKS) { sink ->
            sink.condition.markFree()?.let { sink.copy(condition = it, trackFactsReachAnalysisEnd = emptyList()) }
        }

    override fun sinkRulesForMethodEntry(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintMethodEntrySink> =
        base.entryPointRulesForMethod(method, statement, fact, allRelevant).derived(Derivation.SOURCE_SINKS) { source ->
            sourceSink(source) { c, id, meta ->
                TaintMethodEntrySink(source.method, c, emptyList(), id, meta, source.info, source.serializedId)
            }
        } + base.sinkRulesForMethodEntry(method, statement, fact, allRelevant).derived(Derivation.RESIDUAL_SINKS) { sink ->
            sink.condition.markFree()?.let { sink.copy(condition = it, trackFactsReachAnalysisEnd = emptyList()) }
        }

    override fun sinkRulesForMethodExit(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, initialFacts: Set<InitialFactAp>?, allRelevant: Boolean
    ): Iterable<TaintMethodExitSink> {
        val sinks = base.sinkRulesForMethodExit(method, statement, fact, initialFacts = emptySet(), allRelevant)
        return base.exitSourceRulesForMethod(method, statement, fact, allRelevant).derived(Derivation.SOURCE_SINKS) { source ->
            sourceSink(source) { c, id, meta ->
                TaintMethodExitSink(source.method, c, emptyList(), id, meta, source.info, source.serializedId)
            }
        } + sinks.derived(Derivation.RESIDUAL_SINKS) { sink ->
            sink.condition.markFree()?.let { sink.copy(condition = it, trackFactsReachAnalysisEnd = emptyList()) }
        }
    }

    fun sinkRulesForStaticField(field: JIRField, statement: CommonInst): List<TaintMethodSink> {
        val method = statement.location.method
        return base.sourceRulesForStaticField(field, statement, fact = null).flatMap { source ->
            derive(Derivation.SOURCE_SINKS, source to method) {
                listOfNotNull(sourceSink(source) { c, id, meta ->
                    TaintMethodSink(method, c, emptyList(), id, meta, source.info, source.serializedId)
                })
            }
        }
    }

    override fun sourceRulesForStaticField(
        field: JIRField, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintStaticFieldSource> =
        base.sourceRulesForStaticField(field, statement, fact, allRelevant).derived(Derivation.CONDITIONAL_SOURCES) {
            conditionalSource(it, dropResult = true) { c, a -> it.copy(condition = c, actionsAfter = a) }
        }

    override fun passTroughRulesForMethod(
        method: CommonMethod, statement: CommonInst?, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintPassThrough> = base.passTroughRulesForMethod(method, statement, fact, allRelevant)

    override fun cleanerRulesForMethod(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintCleaner> =
        base.cleanerRulesForMethod(method, statement, fact, allRelevant).derived(Derivation.CLEANERS) { rule ->
            rule.condition.markFree()?.let { rule.copy(condition = it) }
        }

    override fun selectRules(ruleIds: Set<String>) = base.selectRules(ruleIds)

    override fun sinkMetaForSource(source: TaintConfigurationSource): Pair<String, TaintSinkMeta>? =
        base.sinkMetaForSource(source)

    @Suppress("UNCHECKED_CAST")
    private inline fun <T> derive(kind: Derivation, rule: Any, crossinline body: () -> List<T>): List<T> =
        cache.computeIfAbsent(kind to rule) { body() as List<Any> } as List<T>

    private inline fun <R : Any, T> Iterable<R>.derived(kind: Derivation, crossinline body: (R) -> T?): List<T> =
        flatMap { rule -> derive(kind, rule) { listOfNotNull(body(rule)) } }

    private inline fun <T> sourceSink(
        source: TaintConfigurationSource,
        create: (Condition, String, TaintSinkMeta) -> T,
    ): T? {
        val condition = source.condition.markFree() ?: return null
        if (source.actionsAfter.isEmpty()) return null

        val (id, meta) = base.sinkMetaForSource(source) ?: syntheticMeta(source)
        return create(conjunction(listOf(condition, source.produced())), id, meta)
    }

    private inline fun <T> conditionalSource(
        source: TaintConfigurationSource,
        dropResult: Boolean,
        create: (Condition, List<AssignMark>) -> T,
    ): T? {
        val (condition, marks) = source.condition.markDemands(dropResult) ?: return null
        if (source.actionsAfter.isEmpty()) return null
        return create(conjunction(listOf(condition, source.produced())), marks)
    }

    private inline fun <T> sinkSource(
        sink: TaintConfigurationSink,
        dropResult: Boolean,
        create: (Condition, List<AssignMark>) -> T,
    ): T? =
        sink.condition.markDemands(dropResult)?.let { (condition, marks) -> create(condition, marks) }

    private fun Condition.markFree(): Condition? {
        val nnf = simplify()
        if (nnf.positiveMarks().isNotEmpty()) return null
        return nnf.withoutMarks().takeUnless { it.isFalse() }
    }

    private fun Condition.markDemands(dropResult: Boolean): Pair<Condition, List<AssignMark>>? {
        val nnf = simplify()
        val marks = nnf.positiveMarks()
            .filter { !dropResult || it.position.resolveBaseAp() != AccessPathBase.Return }
            .distinct()
        val condition = nnf.withoutMarks()
        if (marks.isEmpty() || condition.isFalse()) return null
        return condition to marks
    }

    private fun Condition.withoutMarks(): Condition = when (this) {
        is CommonCondition.True -> this
        is CommonCondition.Atom -> if (atom.markActions() != null) mkTrue() else this
        is CommonCondition.Not -> if ((arg as? CommonCondition.Atom)?.atom?.markActions() != null) mkTrue() else this
        is CommonCondition.And -> conjunction(args.map { it.withoutMarks() })
        is CommonCondition.Or -> args.map { it.withoutMarks() }
            .junction(absorbing = mkTrue(), neutral = mkFalse(), ::mkOr) { (it as? CommonCondition.Or)?.args }
    }

    private fun conjunction(args: List<Condition>): Condition =
        args.junction(absorbing = mkFalse(), neutral = mkTrue(), ::mkAnd) { (it as? CommonCondition.And)?.args }

    private inline fun List<Condition>.junction(
        absorbing: Condition,
        neutral: Condition,
        make: (List<Condition>) -> Condition,
        operands: (Condition) -> List<Condition>?,
    ): Condition {
        val args = flatMap { operands(it) ?: listOf(it) }.filter { it != neutral }.distinct()
        return if (absorbing in args) absorbing else make(args)
    }

    private fun TaintConfigurationSource.produced(): Condition = mkOr(actionsAfter.map { it.contained() })

    private fun AssignMark.contained(): Condition {
        val position = position
        if (position is PositionWithAccess && position.access == PositionAccessor.AnyFieldAccessor) {
            return CommonCondition.Atom(ContainsMarkOnAnyField(position.base, mark))
        }
        return CommonCondition.Atom(ContainsMark(position, mark))
    }

    private fun syntheticMeta(source: TaintConfigurationSource): Pair<String, TaintSinkMeta> {
        val id = source.serializedId ?: source.actionsAfter.joinToString(",") { it.mark.name }
        return id to TaintSinkMeta(message = "", CommonTaintConfigurationSinkMeta.Severity.Warning, cwe = null)
    }

    companion object {
        private fun JirCondition.markActions(): List<AssignMark>? = when (this) {
            is ContainsMark -> listOf(AssignMark(mark, position))
            is ContainsMarkOnAnyField -> listOf(
                AssignMark(mark, position),
                AssignMark(mark, PositionWithAccess(position, PositionAccessor.AnyFieldAccessor)),
            )
            else -> null
        }

        fun Condition.positiveMarks(): List<AssignMark> = when (this) {
            is CommonCondition.Atom -> atom.markActions().orEmpty()
            is CommonCondition.And -> args.flatMap { it.positiveMarks() }
            is CommonCondition.Or -> args.flatMap { it.positiveMarks() }
            is CommonCondition.True, is CommonCondition.Not -> emptyList()
        }
    }
}
