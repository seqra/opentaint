package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.configuration.CommonTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardFindingTracker.BackwardDemandSeed
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardFindingTracker.BackwardSourceFinding
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardFindingTracker.BackwardUnconditionalSink
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr
import org.opentaint.dataflow.taint.TaintSourceActionPreconditionEvaluator
import org.opentaint.dataflow.taint.evaluateSourceRulePrecondition
import org.opentaint.dataflow.taint.mkAccessPath
import org.opentaint.dataflow.taint.removeNegated
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst

class JIRBackwardTaintRules(
    private val apManager: ApManager,
    private val context: JIRBackwardMethodAnalysisContext,
) {
    sealed interface SinkDemand {
        val rule: TaintConfigurationSink

        data class Seed(override val rule: TaintConfigurationSink, val fact: FinalFactAp) : SinkDemand
        data class Unconditional(override val rule: TaintConfigurationSink) : SinkDemand
    }

    sealed interface SourceMatch {
        val rule: TaintConfigurationSource
        val marks: Set<TaintMarkAccessor>

        data class Found(
            override val rule: TaintConfigurationSource,
            override val marks: Set<TaintMarkAccessor>,
        ) : SourceMatch

        data class ConditionDemand(
            override val rule: TaintConfigurationSource,
            override val marks: Set<TaintMarkAccessor>,
            val facts: List<FinalFactAp>,
        ) : SourceMatch
    }

    class SourceMatchResult(
        val matches: List<SourceMatch>,
        val reader: FinalFactReader?,
    ) {
        val found: List<SourceMatch.Found>
            get() = matches.filterIsInstance<SourceMatch.Found>()

        val conditionDemands: List<FinalFactAp>
            get() = matches.filterIsInstance<SourceMatch.ConditionDemand>().flatMap { it.facts }

        companion object {
            val EMPTY = SourceMatchResult(emptyList(), reader = null)
        }
    }

    private val taint get() = context.taint
    private val factTypeChecker get() = context.factTypeChecker

    fun callSinkDemands(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
    ): List<SinkDemand> {
        val rules = taint.sinkRulesForCallStatement(statement, callExpr, returnValue, fact = null)
        return sinkDemands(rules) { calleeFact -> mapCalleeToCaller(statement, calleeFact) }
    }

    fun methodExitSinkDemands(statement: JIRReturnInst): List<SinkDemand> {
        val rules = taint.sinkRulesForMethodExit(statement, fact = null, initialFacts = null)
        return sinkDemands(rules) { fact -> mapMethodExitFact(statement, fact) }
    }

    fun methodEntrySinkDemands(statement: JIRInst): List<SinkDemand> {
        val rules = taint.sinkRulesForMethodEntry(statement, fact = null)
        return sinkDemands(rules) { fact -> fact.takeIf { isMethodBoundaryBase(it.base) } }
    }

    fun recordSinkDemands(statement: JIRInst, demands: List<SinkDemand>): List<FinalFactAp> {
        val seeds = mutableListOf<FinalFactAp>()
        for (demand in demands) {
            when (demand) {
                is SinkDemand.Seed -> {
                    context.findings.addDemandSeed(
                        BackwardDemandSeed(context.methodEntryPoint, statement, demand.rule, demand.fact)
                    )
                    seeds += demand.fact
                }

                is SinkDemand.Unconditional -> context.findings.addUnconditionalSink(
                    BackwardUnconditionalSink(context.methodEntryPoint, statement, demand.rule)
                )
            }
        }
        return seeds
    }

    fun matchCallSources(
        statement: JIRInst,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        callerFact: FinalFactAp,
        startBase: AccessPathBase,
    ): SourceMatchResult {
        val rules = taint.sourceRulesForCallStatement(statement, callExpr, returnValue, fact = null)
        if (rules.isEmpty()) return SourceMatchResult.EMPTY

        val reader = FinalFactReader(callerFact.rebase(startBase), apManager)
        return matchSources(rules, reader) { calleeFact -> mapCalleeToCaller(statement, calleeFact) }
    }

    fun matchMethodExitSources(statement: JIRReturnInst, fact: FinalFactAp): SourceMatchResult {
        val rules = taint.sourceRulesForMethodExit(statement, fact = null)
        if (rules.isEmpty()) return SourceMatchResult.EMPTY

        val reader = FinalFactReader(fact, apManager)
        return matchSources(rules, reader) { conditionFact -> mapMethodExitFact(statement, conditionFact) }
    }

    fun matchMethodEntrySources(statement: JIRInst, fact: FinalFactAp): SourceMatchResult {
        if (fact.base !is AccessPathBase.Argument && fact.base !is AccessPathBase.This) {
            return SourceMatchResult.EMPTY
        }

        val rules = taint.sourceRulesForMethodEntry(statement, fact = null)
        if (rules.isEmpty()) return SourceMatchResult.EMPTY

        val reader = FinalFactReader(fact, apManager)
        return matchSources(rules, reader) { conditionFact ->
            conditionFact.takeIf { isMethodBoundaryBase(it.base) }
        }
    }

    fun recordMethodEntrySourceMatches(statement: JIRInst, result: SourceMatchResult, initialFacts: Set<InitialFactAp>) {
        if (result.found.isEmpty()) return
        if (initialFacts.isNotEmpty() && initialFacts.all { leavesThroughArgumentRoot(statement, it) }) return
        recordSourceMatches(statement, result)
    }

    private fun leavesThroughArgumentRoot(statement: JIRInst, initialFact: InitialFactAp): Boolean {
        val base = initialFact.base
        if (base !is AccessPathBase.Argument && base !is AccessPathBase.This) return false
        return methodEntryMarks(statement).any { initialFact.startsWithAccessor(it) }
    }

    private fun methodEntryMarks(statement: JIRInst): Set<TaintMarkAccessor> =
        taint.sourceRulesForMethodEntry(statement, fact = null).flatMapTo(hashSetOf()) { ruleWithCondition ->
            ruleWithCondition.rule.actionsAfter.map { TaintMarkAccessor(it.mark.name) }
        }

    fun matchStaticFieldSources(statement: JIRAssignInst, fact: FinalFactAp): SourceMatchResult {
        val fieldRef = statement.rhv as? JIRFieldRef ?: return SourceMatchResult.EMPTY
        val field = fieldRef.field.field
        if (!field.isStatic) return SourceMatchResult.EMPTY

        val lhv = accessPathBase(statement.lhv) ?: return SourceMatchResult.EMPTY
        if (fact.base != lhv) return SourceMatchResult.EMPTY

        val rules = taint.sourceRulesForStaticField(field, statement, fact = null)
        if (rules.isEmpty()) return SourceMatchResult.EMPTY

        val reader = FinalFactReader(fact.rebase(AccessPathBase.Return), apManager)
        return matchSources(rules, reader) { null }
    }

    fun recordSourceMatches(statement: JIRInst, result: SourceMatchResult) {
        for (match in result.found) {
            for (mark in match.marks) {
                context.findings.addSourceFinding(
                    BackwardSourceFinding(context.methodEntryPoint, statement, match.rule, mark)
                )
            }
        }
    }

    fun mapCalleeToCaller(statement: JIRInst, calleeFact: FinalFactAp): FinalFactAp? =
        JIRBackwardMethodCallFactMapper
            .mapMethodExitToReturnFlowFact(statement, calleeFact, factTypeChecker)
            .singleOrNull()

    private fun mapMethodExitFact(statement: JIRReturnInst, fact: FinalFactAp): FinalFactAp? {
        if (fact.base != AccessPathBase.Return) {
            return fact.takeIf { isMethodBoundaryBase(it.base) }
        }

        val returnValue = statement.returnValue ?: return null
        val returnBase = accessPathBase(returnValue) ?: return null
        if (returnBase is AccessPathBase.Constant) return null

        return fact.rebase(returnBase)
    }

    private fun isMethodBoundaryBase(base: AccessPathBase): Boolean =
        JIRBackwardMethodCallFactMapper.isValidMethodExitFactBase(base)

    private inline fun <R : TaintConfigurationSink> sinkDemands(
        rules: List<RuleWithCondition<R>>,
        mapFact: (FinalFactAp) -> FinalFactAp?,
    ): List<SinkDemand> {
        if (rules.isEmpty()) return emptyList()

        val result = mutableListOf<SinkDemand>()
        for (ruleWithCondition in rules) {
            val rule = ruleWithCondition.rule
            val condition = ruleWithCondition.condition
            if (condition.isFalse) continue

            val positiveExpr = if (condition.isTrue) null else condition.expr.removeNegated()
            if (positiveExpr == null) {
                result += SinkDemand.Unconditional(rule)
                continue
            }

            for (fact in positiveExpr.demandFacts()) {
                val mapped = mapFact(fact) ?: continue
                result += SinkDemand.Seed(rule, mapped)
            }
        }
        return result
    }

    private fun <R : TaintConfigurationSource> matchSources(
        rules: List<RuleWithCondition<R>>,
        reader: FinalFactReader,
        mapConditionFact: (FinalFactAp) -> FinalFactAp?,
    ): SourceMatchResult {
        val evaluator = TaintSourceActionPreconditionEvaluator(reader)
        val matches = mutableListOf<SourceMatch>()

        for (ruleWithCondition in rules) {
            evaluateSourceRulePrecondition(
                ruleWithCondition,
                ruleWithCondition.rule.actionsAfter,
                evaluator,
                evalAction = { r, a -> evaluate(r, a, a.position.resolveAp(), TaintMarkAccessor(a.mark.name)) },
                mkSource = { r, actions -> matches += SourceMatch.Found(r, actions.marks()) },
                mkPass = { r, actions, expr ->
                    val facts = expr.demandFacts().mapNotNull(mapConditionFact)
                    matches += SourceMatch.ConditionDemand(r, actions.marks(), facts)
                },
            )
        }

        return SourceMatchResult(matches, reader)
    }

    private fun Set<CommonTaintAssignAction>.marks(): Set<TaintMarkAccessor> =
        mapTo(hashSetOf()) { TaintMarkAccessor((it as AssignMark).mark.name) }

    private fun TaintMarkAwareConditionExpr.demandFacts(): List<FinalFactAp> {
        val positions = mutableListOf<Pair<PositionAccess, TaintMarkAccessor>>()
        collectPositiveMarkPositions(positions)
        return positions.distinct().map { (position, mark) -> apManager.mkAccessPath(position, ExclusionSet.Universe, mark) }
    }

    private fun TaintMarkAwareConditionExpr.collectPositiveMarkPositions(
        result: MutableList<Pair<PositionAccess, TaintMarkAccessor>>
    ) {
        when (this) {
            is TaintMarkAwareConditionExpr.And -> args.forEach { it.collectPositiveMarkPositions(result) }
            is TaintMarkAwareConditionExpr.Or -> args.forEach { it.collectPositiveMarkPositions(result) }
            is TaintMarkAwareConditionExpr.ContainsMarkLiteral -> if (!negated) result += position to mark
            is TaintMarkAwareConditionExpr.ContainsMarkOnAnyAccessorLiteral -> if (!negated) {
                result += position to mark
                result += PositionAccess.Complex(position, AnyAccessor) to mark
            }
        }
    }
}
