package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition.PassRuleCondition
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintAssignAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSource
import org.opentaint.dataflow.util.cartesianProductMapTo
import org.opentaint.util.Maybe
import org.opentaint.util.maybeFlatMap

fun <R : CommonTaintConfigurationSource, A : CommonTaintAssignAction, C> evaluateSourceRulePrecondition(
    rule: R,
    ruleActions: List<A>,
    ruleCondition: R.() -> CommonCondition<C>,
    sourcePreconditionEvaluator: TaintSourceActionPreconditionEvaluator,
    evalAction: TaintSourceActionPreconditionEvaluator.(R, A) -> Maybe<List<Pair<CommonTaintConfigurationItem, CommonTaintAssignAction>>>,
    conditionRewriter: RuleConditionRewriter<C>,
): List<TaintRulePrecondition> {
    val result = mutableListOf<TaintRulePrecondition>()
    evaluateSourceRulePrecondition(
        rule, ruleActions, ruleCondition, sourcePreconditionEvaluator, evalAction, conditionRewriter,
        mkSource = { r, a -> result += TaintRulePrecondition.Source(r, a) },
        mkPass = { r, a, e -> result += TaintRulePrecondition.Pass(r, a, PassRuleCondition.Expr(e)) }
    )
    return result
}

fun <R: CommonTaintConfigurationSource, A: CommonTaintAssignAction, C> evaluateSourceRulePrecondition(
    rule: R,
    ruleActions: List<A>,
    ruleCondition: R.() -> CommonCondition<C> ,
    sourcePreconditionEvaluator: TaintSourceActionPreconditionEvaluator,
    evalAction: TaintSourceActionPreconditionEvaluator.(R, A) -> Maybe<List<Pair<CommonTaintConfigurationItem, CommonTaintAssignAction>>>,
    conditionRewriter: RuleConditionRewriter<C>,
    mkSource: (R, Set<CommonTaintAssignAction>) -> Unit,
    mkPass: (R, Set<CommonTaintAssignAction>, TaintMarkAwareConditionExpr) -> Unit,
) {
    val assignedMarks = ruleActions.maybeFlatMap {
        sourcePreconditionEvaluator.evalAction(rule, it)
    }
    if (assignedMarks.isNone) return

    val sourceActions = assignedMarks.getOrThrow().mapTo(hashSetOf()) { it.second }

    val simplifiedCondition = conditionRewriter.rewrite(rule.ruleCondition())

    val simplifiedExpr = when {
        simplifiedCondition.isFalse -> return
        simplifiedCondition.isTrue -> null
        else -> simplifiedCondition.expr
    }

    // We always treat negated mark condition as satisfied
    val exprWithoutNegations = simplifiedExpr?.removeNegated()
    if (exprWithoutNegations == null) {
        mkSource(rule, sourceActions)
        return
    }

    mkPass(rule, sourceActions, exprWithoutNegations)
}

fun  <R: CommonTaintConfigurationItem, A: CommonTaintAction, C> evaluatePassRulePrecondition(
    rule: R,
    ruleActions: List<A>,
    ruleCondition: R.() -> CommonCondition<C>,
    preconditionEvaluator: TaintPassActionPreconditionEvaluator,
    evalAction: TaintPassActionPreconditionEvaluator.(R, A) -> Maybe<List<Pair<CommonTaintAction, InitialFactAp>>>,
    conditionRewriter: RuleConditionRewriter<C>,
    mapExit2Return: (InitialFactAp) -> List<InitialFactAp>,
): List<TaintRulePrecondition> {
    val actions = ruleActions.maybeFlatMap {
        preconditionEvaluator.evalAction(rule, it)
    }
    if (actions.isNone) return emptyList()

    val passActions = actions.getOrThrow()

    val simplifiedCondition = conditionRewriter.rewrite(rule.ruleCondition())

    val simplifiedExpr = when {
        simplifiedCondition.isFalse -> return emptyList()
        simplifiedCondition.isTrue -> null
        else -> simplifiedCondition.expr
    }

    // We always treat negated mark condition as satisfied
    val exprWithoutNegations = simplifiedExpr?.removeNegated()

    val mappedAction = passActions.flatMap { (action, fact) ->
        mapExit2Return(fact).map { action to it }
    }

    return mappedAction.map { (action, fact) ->
        val cond = if (exprWithoutNegations == null) {
            PassRuleCondition.Fact(fact)
        } else {
            PassRuleCondition.FactWithExpr(fact, exprWithoutNegations)
        }
        TaintRulePrecondition.Pass(rule, setOf(action), cond)
    }
}

fun TaintMarkAwareConditionExpr.removeNegated() = removeTrueLiterals { it.negated }

private fun createPositionWithTaintMark(
    apManager: ApManager,
    position: PositionAccess,
    mark: TaintMarkAccessor,
): InitialFactAp {
    val positionWithMark = PositionAccess.Complex(position, mark)
    val finalPositionWithMark = PositionAccess.Complex(positionWithMark, FinalAccessor)
    return createPosition(apManager, finalPositionWithMark)
}

private fun createPosition(apManager: ApManager, position: PositionAccess): InitialFactAp {
    var normalizedPosition = position
    if (position is PositionAccess.Complex && position.accessor is FinalAccessor) {
        // mkInitialAccessPath starts with final ap
        normalizedPosition = position.base
    }
    return apManager.mkInitialAccessPath(normalizedPosition, ExclusionSet.Universe)
}

data class PreconditionCube(val facts: Set<InitialFactAp>)

fun TaintMarkAwareConditionExpr.preconditionDnf(
    apManager: ApManager,
    mapFacts: (InitialFactAp) -> List<InitialFactAp>,
): List<PreconditionCube> = when (this) {
    is TaintMarkAwareConditionExpr.ContainsMarkLiteral -> {
        val preconditionFact = createPositionWithTaintMark(apManager, position, mark)
        mapFacts(preconditionFact).map { PreconditionCube(setOf(it)) }
    }

    is TaintMarkAwareConditionExpr.ContainsMarkOnAnyAccessorLiteral -> {
        TODO("ContainsMarkOnAnyAccessor is not supported for non-sink rule preconditions")
    }

    is TaintMarkAwareConditionExpr.Or -> args.flatMap { it.preconditionDnf(apManager, mapFacts) }
    is TaintMarkAwareConditionExpr.And -> {
        val result = mutableListOf<PreconditionCube>()
        val cubeLists = args.map { it.preconditionDnf(apManager, mapFacts) }
        cubeLists.cartesianProductMapTo { cubes ->
            val facts = hashSetOf<InitialFactAp>()
            cubes.flatMapTo(facts) { it.facts }
            result += PreconditionCube(facts)
        }
        result
    }
}
