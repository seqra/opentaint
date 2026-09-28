package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.Condition
import org.opentaint.dataflow.configuration.jvm.ContainsMark
import org.opentaint.dataflow.configuration.jvm.CopyMark
import org.opentaint.dataflow.configuration.jvm.JirCondition
import org.opentaint.dataflow.configuration.jvm.PositionAccessor
import org.opentaint.dataflow.configuration.jvm.PositionWithAccess
import org.opentaint.dataflow.configuration.jvm.RemoveMark
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMark
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.configuration.jvm.TaintSinkMeta
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.dataflow.configuration.jvm.serialized.ItemInfo
import org.opentaint.dataflow.configuration.jvm.serialized.UserDefinedRuleInfo
import org.opentaint.dataflow.configuration.mkAnd
import org.opentaint.dataflow.configuration.mkOr
import org.opentaint.dataflow.configuration.simplify
import org.opentaint.dataflow.jvm.ap.ifds.taint.ContainsMarkOnAnyField
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveBaseAp
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.JIRField
import java.util.concurrent.ConcurrentHashMap

class JIRBackwardTaintRulesProvider(private val base: TaintRulesProvider) : TaintRulesProvider {
    private enum class Derivation { SOURCE_SINKS, SINK_SOURCES, CONDITIONAL_SOURCES, RESIDUAL_SINKS, SHADOW }

    private val derived = ConcurrentHashMap<Pair<Derivation, Any>, List<Any>>()

    override fun entryPointRulesForMethod(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintEntryPointSource> = emptyList()

    override fun sourceRulesForMethod(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintMethodSource> {
        val sources = base.sourceRulesForMethod(method, statement, fact, allRelevant)
        if (allRelevant) return sources.map { it.withShadowInfo() }

        val sinks = base.sinkRulesForMethod(method, statement, fact, allRelevant)
        return sinks.flatMap { sink ->
            derive(Derivation.SINK_SOURCES, sink) {
                sinkSources(sink, shadow = false, callSite = true) { condition, actions ->
                    TaintMethodSource(sink.method, condition, actions, sink.info, sink.serializedId)
                }
            }
        } + sources.flatMap { source ->
            derive(Derivation.CONDITIONAL_SOURCES, source) {
                conditionalSources(source, callSite = true) { condition, actions ->
                    source.copy(condition = condition, actionsAfter = actions)
                }
            }
        }
    }

    override fun exitSourceRulesForMethod(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintMethodExitSource> {
        val sinks = base.sinkRulesForMethodExit(method, statement, fact, initialFacts = emptySet(), allRelevant)
        return sinks.flatMap { sink ->
            derive(Derivation.SINK_SOURCES, sink) {
                sinkSources(sink, shadow = true, callSite = false) { condition, actions ->
                    TaintMethodExitSource(sink.method, condition, actions, sink.info, sink.serializedId)
                }
            }
        } + base.exitSourceRulesForMethod(method, statement, fact, allRelevant).flatMap { source ->
            derive(Derivation.CONDITIONAL_SOURCES, source) {
                conditionalSources(source, callSite = false) { condition, actions ->
                    source.copy(condition = condition, actionsAfter = actions)
                }
            }
        }
    }

    override fun sinkRulesForMethod(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintMethodSink> =
        base.sourceRulesForMethod(method, statement, fact, allRelevant).flatMap { source ->
            derive(Derivation.SOURCE_SINKS, source) {
                sourceSinks(source) { condition, id, meta ->
                    TaintMethodSink(source.method, condition, emptyList(), id, meta, source.info, source.serializedId)
                }
            }
        } + base.sinkRulesForMethod(method, statement, fact, allRelevant).flatMap { sink ->
            derive(Derivation.RESIDUAL_SINKS, sink) {
                residualSinks(sink) { sink.copy(condition = it, trackFactsReachAnalysisEnd = emptyList()) }
            }
        }

    override fun sinkRulesForMethodEntry(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintMethodEntrySink> =
        base.entryPointRulesForMethod(method, statement, fact, allRelevant).flatMap { source ->
            derive(Derivation.SOURCE_SINKS, source) {
                sourceSinks(source) { condition, id, meta ->
                    TaintMethodEntrySink(source.method, condition, emptyList(), id, meta, source.info, source.serializedId)
                }
            }
        } + base.sinkRulesForMethodEntry(method, statement, fact, allRelevant).flatMap { sink ->
            derive(Derivation.RESIDUAL_SINKS, sink) {
                residualSinks(sink) { sink.copy(condition = it, trackFactsReachAnalysisEnd = emptyList()) }
            }
        }

    override fun sinkRulesForMethodExit(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, initialFacts: Set<InitialFactAp>?, allRelevant: Boolean
    ): Iterable<TaintMethodExitSink> =
        base.exitSourceRulesForMethod(method, statement, fact, allRelevant).flatMap { source ->
            derive(Derivation.SOURCE_SINKS, source) {
                sourceSinks(source) { condition, id, meta ->
                    TaintMethodExitSink(source.method, condition, emptyList(), id, meta, source.info, source.serializedId)
                }
            }
        }

    fun sinkRulesForStaticField(field: JIRField, statement: CommonInst): List<TaintMethodSink> {
        val method = statement.location.method
        return base.sourceRulesForStaticField(field, statement, fact = null).flatMap { source ->
            derive(Derivation.SOURCE_SINKS, source to method) {
                sourceSinks(source) { condition, id, meta ->
                    TaintMethodSink(method, condition, emptyList(), id, meta, source.info, source.serializedId)
                }
            }
        }
    }

    override fun sourceRulesForStaticField(
        field: JIRField, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintStaticFieldSource> = emptyList()

    override fun passTroughRulesForMethod(
        method: CommonMethod, statement: CommonInst?, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintPassThrough> =
        base.passTroughRulesForMethod(method, statement, fact, allRelevant).map { rule ->
            val copies = rule.actionsAfter.filterIsInstance<CopyMark>()
            if (copies.isEmpty()) return@map rule
            derive(Derivation.SHADOW, rule) {
                listOf(rule.copy(actionsAfter = rule.actionsAfter + copies.map { it.copy(mark = it.mark.shadow()) }))
            }.single()
        }

    override fun cleanerRulesForMethod(
        method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
    ): Iterable<TaintCleaner> =
        base.cleanerRulesForMethod(method, statement, fact, allRelevant).map { rule ->
            derive(Derivation.SHADOW, rule) {
                val removals = rule.actionsAfter.filterIsInstance<RemoveMark>().map { it.copy(mark = it.mark.shadow()) }
                listOf(
                    rule.copy(
                        condition = rule.condition.withShadowMarks(),
                        actionsAfter = rule.actionsAfter + removals,
                        info = rule.info.withShadowMarks(),
                    )
                )
            }.single()
        }

    override fun selectRules(ruleIds: Set<String>) = base.selectRules(ruleIds)

    override fun sinkMetaForSource(source: TaintConfigurationSource): Pair<String, TaintSinkMeta>? =
        base.sinkMetaForSource(source)

    private fun TaintMethodSource.withShadowInfo(): TaintMethodSource {
        if (info !is UserDefinedRuleInfo) return this
        return derive(Derivation.SHADOW, this) { listOf(copy(info = info.withShadowMarks())) }.single()
    }

    @Suppress("UNCHECKED_CAST")
    private inline fun <T> derive(kind: Derivation, rule: Any, crossinline body: () -> List<T>): List<T> =
        derived.computeIfAbsent(kind to rule) { body() as List<Any> } as List<T>

    private inline fun <T> sourceSinks(
        source: TaintConfigurationSource,
        create: (Condition, String, TaintSinkMeta) -> T,
    ): List<T> {
        val unconditional = source.condition.cubes().filter { it.marks.isEmpty() }
        if (unconditional.isEmpty() || source.actionsAfter.isEmpty()) return emptyList()

        val produced = source.actionsAfter.flatMap { listOf(it.contained(it.mark), it.contained(it.mark.shadow())) }
        val condition = mkAnd(listOf(mkOr(unconditional.map { mkAnd(it.rest.toList()) }), mkOr(produced)))
        val (id, meta) = base.sinkMetaForSource(source) ?: syntheticMeta(source)
        return listOf(create(condition, id, meta))
    }

    private inline fun <T> conditionalSources(
        source: TaintConfigurationSource,
        callSite: Boolean,
        create: (Condition, List<AssignMark>) -> T,
    ): List<T> = source.condition.cubes()
        .filter { it.marks.isNotEmpty() && !(callSite && it.demandsResult()) }
        .flatMap { cube ->
            listOf(false, true).map { shadow ->
                val produced = mkOr(source.actionsAfter.map { it.contained(it.mark.shadowIf(shadow)) })
                create(mkAnd(cube.rest.toList() + produced), cube.actions(shadow))
            }
        }

    private inline fun <T> sinkSources(
        sink: TaintConfigurationSink,
        shadow: Boolean,
        callSite: Boolean,
        create: (Condition, List<AssignMark>) -> T,
    ): List<T> {
        val requirement = endRequirement(sink)?.let { it.contained(it.mark) }
        return sink.condition.cubes()
            .filter { it.marks.isNotEmpty() && !(callSite && it.demandsResult()) }
            .map { cube ->
                create(mkAnd(cube.rest.toList() + listOfNotNull(requirement)), cube.actions(shadow))
            }
    }

    private inline fun <T> residualSinks(sink: TaintConfigurationSink, create: (Condition) -> T): List<T> {
        val requirement = endRequirement(sink)?.let { it.contained(it.mark) }
        val cubes = sink.condition.cubes().filter { it.marks.isEmpty() }
        if (cubes.isEmpty()) return emptyList()
        return listOf(create(mkOr(cubes.map { mkAnd(it.rest.toList() + listOfNotNull(requirement)) })))
    }

    private fun syntheticMeta(source: TaintConfigurationSource): Pair<String, TaintSinkMeta> {
        val id = source.serializedId ?: source.actionsAfter.joinToString(",") { it.mark.name }
        return id to TaintSinkMeta(message = "", CommonTaintConfigurationSinkMeta.Severity.Warning, cwe = null)
    }

    private class Cube(val marks: Set<JirCondition>, val rest: Set<Condition>) {
        operator fun plus(other: Cube) = Cube(marks + other.marks, rest + other.rest)

        fun subsumes(other: Cube): Boolean = other.marks.containsAll(marks) && other.rest.containsAll(rest)

        fun actions(shadow: Boolean): List<AssignMark> = marks.flatMap { it.markActions().orEmpty() }
            .map { it.copy(mark = it.mark.shadowIf(shadow)) }
            .distinct()

        fun demandsResult(): Boolean =
            marks.any { atom -> atom.markActions().orEmpty().any { it.position.resolveBaseAp() == AccessPathBase.Return } }
    }

    private fun Condition.cubes(): List<Cube> {
        val cubes = simplify().nnfCubes().distinctBy { it.marks to it.rest }
        return cubes.filter { cube -> cubes.none { it !== cube && it.subsumes(cube) && !cube.subsumes(it) } }
    }

    private fun Condition.nnfCubes(): List<Cube> = when (this) {
        is CommonCondition.True -> listOf(EMPTY_CUBE)
        is CommonCondition.Atom -> listOf(if (atom.markActions() != null) Cube(setOf(atom), emptySet()) else Cube(emptySet(), setOf(this)))
        is CommonCondition.Not -> when (val arg = arg) {
            is CommonCondition.True -> emptyList()
            is CommonCondition.Atom -> listOf(if (arg.atom.markActions() != null) EMPTY_CUBE else Cube(emptySet(), setOf(this)))
            else -> error("Condition is not in NNF: $this")
        }
        is CommonCondition.And -> args.fold(listOf(EMPTY_CUBE)) { cubes, arg ->
            val argCubes = arg.nnfCubes()
            cubes.flatMap { cube -> argCubes.map { cube + it } }
        }
        is CommonCondition.Or -> args.flatMap { it.nnfCubes() }
    }

    private fun AssignMark.contained(mark: TaintMark): Condition {
        val position = position
        if (position is PositionWithAccess && position.access == PositionAccessor.AnyFieldAccessor) {
            return CommonCondition.Atom(ContainsMarkOnAnyField(position.base, mark))
        }
        return CommonCondition.Atom(ContainsMark(position, mark))
    }

    private fun Condition.withShadowMarks(): Condition = when (this) {
        is CommonCondition.True -> this
        is CommonCondition.Atom -> when (val atom = atom) {
            is ContainsMark -> mkOr(listOf(this, CommonCondition.Atom(atom.copy(mark = atom.mark.shadow()))))
            is ContainsMarkOnAnyField -> mkOr(listOf(this, CommonCondition.Atom(atom.copy(mark = atom.mark.shadow()))))
            else -> this
        }
        is CommonCondition.Not -> CommonCondition.Not(arg.withShadowMarks())
        is CommonCondition.And -> CommonCondition.And(args.map { it.withShadowMarks() })
        is CommonCondition.Or -> CommonCondition.Or(args.map { it.withShadowMarks() })
    }

    private class ShadowRuleInfo(original: UserDefinedRuleInfo) : UserDefinedRuleInfo {
        override val relevantTaintMarks: Set<String> =
            original.relevantTaintMarks + original.relevantTaintMarks.map { TaintMark(it).shadow().name }
    }

    private fun ItemInfo?.withShadowMarks(): ItemInfo? = if (this is UserDefinedRuleInfo) ShadowRuleInfo(this) else this

    companion object {
        private const val SHADOW_SUFFIX = "\$zero-edge"
        private val EMPTY_CUBE = Cube(emptySet(), emptySet())

        private fun JirCondition.markActions(): List<AssignMark>? = when (this) {
            is ContainsMark -> listOf(AssignMark(mark, position))
            is ContainsMarkOnAnyField -> listOf(
                AssignMark(mark, position),
                AssignMark(mark, PositionWithAccess(position, PositionAccessor.AnyFieldAccessor)),
            )
            else -> null
        }

        private fun TaintMark.shadow(): TaintMark = TaintMark(name + SHADOW_SUFFIX)

        private fun TaintMark.shadowIf(shadow: Boolean): TaintMark = if (shadow) shadow() else this

        fun isShadowMark(mark: TaintMarkAccessor): Boolean = mark.mark.endsWith(SHADOW_SUFFIX)

        fun endRequirement(sink: TaintConfigurationSink): AssignMark? =
            sink.trackFactsReachAnalysisEnd.distinct().singleOrNull()

        fun Condition.markPositions(): List<AssignMark> = when (this) {
            is CommonCondition.True -> emptyList()
            is CommonCondition.Atom -> when (val atom = atom) {
                is ContainsMark -> listOf(AssignMark(atom.mark, atom.position))
                is ContainsMarkOnAnyField -> listOf(
                    AssignMark(atom.mark, PositionWithAccess(atom.position, PositionAccessor.AnyFieldAccessor))
                )
                else -> emptyList()
            }
            is CommonCondition.Not -> arg.markPositions()
            is CommonCondition.And -> args.flatMap { it.markPositions() }
            is CommonCondition.Or -> args.flatMap { it.markPositions() }
        }
    }
}
