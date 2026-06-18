package org.opentaint.semgrep.pattern.conversion.python

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.dataflow.configuration.python.serialized.PythonSinkMetaData
import org.opentaint.dataflow.configuration.python.serialized.PythonTarget
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCleaner
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCondition
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonEntryPointSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonRule
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSink
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintAssignAction
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintCleanAction
import org.opentaint.semgrep.pattern.FailedToCreateTaintRules
import org.opentaint.semgrep.pattern.IgnoredMetavarConstraint
import org.opentaint.semgrep.pattern.NonMethodCallCleaner
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.conversion.IsMetavar
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.ParamCondition
import org.opentaint.semgrep.pattern.conversion.SpecificBoolValue
import org.opentaint.semgrep.pattern.conversion.SpecificIntValue
import org.opentaint.semgrep.pattern.conversion.SpecificNullValue
import org.opentaint.semgrep.pattern.conversion.SpecificStringValue
import org.opentaint.semgrep.pattern.conversion.automata.ClassModifierConstraint
import org.opentaint.semgrep.pattern.conversion.automata.MethodConstraint
import org.opentaint.semgrep.pattern.conversion.automata.MethodModifierConstraint
import org.opentaint.semgrep.pattern.conversion.automata.MethodSignature
import org.opentaint.semgrep.pattern.conversion.automata.NumberOfArgsConstraint
import org.opentaint.semgrep.pattern.conversion.automata.ParamConstraint
import org.opentaint.semgrep.pattern.conversion.automata.Position
import org.opentaint.semgrep.pattern.conversion.taint.RuleConversionCtx
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.EdgeCondition
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.EdgeEffect
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.State
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleEdge
import org.opentaint.semgrep.pattern.conversion.taint.isGeneratedAnyValueGenerator
import org.opentaint.semgrep.pattern.conversion.taint.isGeneratedStringConcat

fun PythonTaintRuleGenerationCtx.emitPythonTaintRules(ctx: RuleConversionCtx): List<SerializedPythonRule> {
    val rules = mutableListOf<SerializedPythonRule>()

    fun evaluateWithStateCheck(edge: TaintRuleEdge, stateOfEdge: State): List<PythonEvaluatedEdgeCondition> =
        evaluatePythonMethodConditionAndEffect(stateOfEdge, edge.edgeCondition, edge.edgeEffect, ctx.trace)
            .map { it.addPythonStateCheck(this, edge.checkGlobalState, stateOfEdge) }

    for (ruleEdge in edges) {
        for (condition in evaluateWithStateCheck(ruleEdge, ruleEdge.stateFrom)) {
            val actions = buildPythonStateAssignActions(ruleEdge.stateTo, condition)
            if (actions.isEmpty()) continue

            val target = PythonTarget.Function(condition.ruleCondition.function)
            val cond = condition.ruleCondition.condition.nullIfTrue()
            val info = edgeRuleInfo(ruleEdge).toPython()
            when (ruleEdge.edgeKind) {
                TaintRuleEdge.Kind.MethodCall -> rules += SerializedPythonSource(target, cond, actions, info)
                TaintRuleEdge.Kind.MethodEnter -> rules += SerializedPythonEntryPointSource(target, cond, actions, info)
                TaintRuleEdge.Kind.MethodExit ->
                    ctx.trace.error(FailedToCreateTaintRules("Method-exit sources are not supported yet"))
            }
        }
    }

    for (ruleEdge in edgesToFinalAccept) {
        for (condition in evaluateWithStateCheck(ruleEdge, ruleEdge.stateFrom)) {
            when (ruleEdge.edgeKind) {
                TaintRuleEdge.Kind.MethodCall -> rules += SerializedPythonSink(
                    target = PythonTarget.Function(condition.ruleCondition.function),
                    condition = condition.ruleCondition.condition.nullIfTrue(),
                    meta = ctx.meta.toPythonSinkMeta(),
                )

                TaintRuleEdge.Kind.MethodEnter,
                TaintRuleEdge.Kind.MethodExit ->
                    ctx.trace.error(FailedToCreateTaintRules("Non method call sinks are not supported yet"))
            }
        }
    }

    for (ruleEdge in edgesToFinalDead) {
        for (condition in evaluateWithStateCheck(ruleEdge, ruleEdge.stateFrom)) {
            val actions = buildPythonStateCleanActions(ruleEdge.stateTo, ruleEdge.stateFrom, condition)
            if (actions.isEmpty()) continue

            when (ruleEdge.edgeKind) {
                TaintRuleEdge.Kind.MethodEnter,
                TaintRuleEdge.Kind.MethodExit -> ctx.trace.error(NonMethodCallCleaner())

                TaintRuleEdge.Kind.MethodCall -> rules += SerializedPythonCleaner(
                    target = PythonTarget.Function(condition.ruleCondition.function),
                    condition = condition.ruleCondition.condition.nullIfTrue(),
                    cleans = actions,
                    info = edgeRuleInfo(ruleEdge).toPython(),
                )
            }
        }
    }

    return rules
}

private fun SinkMetaData.toPythonSinkMeta(): PythonSinkMetaData = PythonSinkMetaData(cwe = cwe, note = note)

private fun PythonTaintRuleGenerationCtx.buildPythonStateAssignActions(
    stateAfter: State,
    edgeCondition: PythonEvaluatedEdgeCondition,
): List<SerializedPythonTaintAssignAction> {
    val result = stateAfter.register.assignedVars.keys.flatMapTo(mutableListOf()) { varName ->
        val varPosition = edgeCondition.accessedVarPosition[varName] ?: return@flatMapTo emptyList()
        varPosition.positions.flatMap { stateAssignMark(varPosition.varName, stateAfter, it.baseOnly()) }
    }
    if (stateAfter in globalStateAssignStates) {
        result += globalStateMarkName(stateAfter).mkPythonAssignMark(stateVarPosition)
    }
    return result
}

private fun PythonTaintRuleGenerationCtx.buildPythonStateCleanActions(
    stateAfter: State,
    stateBefore: State,
    edgeCondition: PythonEvaluatedEdgeCondition,
): List<SerializedPythonTaintCleanAction> {
    val result = edgeCondition.accessedVarPosition.values.flatMapTo(mutableListOf()) { varPosition ->
        varPosition.positions.flatMap { stateCleanMark(varPosition.varName, stateAfter, stateBefore, it.baseOnly()) }
    }
    result += stateCleanMark(varName = null, stateAfter, stateBefore, position = null)
    if (stateBefore in globalStateAssignStates) {
        result += globalStateMarkName(stateBefore).mkPythonCleanMark(stateVarPosition)
    }
    return result
}

private fun PythonEvaluatedEdgeCondition.addPythonStateCheck(
    ctx: PythonTaintRuleGenerationCtx,
    checkGlobalState: Boolean,
    stateOfEdge: State,
): PythonEvaluatedEdgeCondition {
    val stateChecks = mutableListOf<SerializedPythonCondition>()
    if (checkGlobalState) {
        stateChecks += ctx.globalStateMarkName(stateOfEdge).mkPythonContainsMark(ctx.stateVarPosition)
    } else {
        for (metaVar in stateOfEdge.register.assignedVars.keys) {
            for (pos in accessedVarPosition[metaVar]?.positions.orEmpty()) {
                stateChecks += ctx.containsStateMark(metaVar, stateOfEdge, pos.baseOnly())
            }
        }
    }

    if (stateChecks.isEmpty()) return this

    val combined = pythonAnd(listOf(pythonOr(stateChecks), ruleCondition.condition))
    return copy(ruleCondition = ruleCondition.copy(condition = combined))
}

private fun PythonTaintRuleGenerationCtx.evaluatePythonMethodConditionAndEffect(
    edgeState: State,
    condition: EdgeCondition,
    effect: EdgeEffect,
    trace: SemgrepRuleLoadStepTrace,
): List<PythonEvaluatedEdgeCondition> {
    val builders = evaluatePythonFormulaSignature(collectSignatures(effect, condition), trace)

    return builders.map { builder ->
        condition.readMetaVar.values.flatten().forEach {
            evaluatePythonEdgePredicateConstraint(edgeState, it.predicate.constraint, it.negated, builder.conditions, trace)
        }
        condition.other.forEach {
            evaluatePythonEdgePredicateConstraint(edgeState, it.predicate.constraint, it.negated, builder.conditions, trace)
        }

        val varPositions = hashMapOf<MetavarAtom, PythonRegisterVarPosition>()
        effect.assignMetaVar.values.flatten().forEach { findPythonMetaVarPosition(it.predicate.constraint, varPositions) }

        PythonEvaluatedEdgeCondition(builder.build(), varPositions)
    }
}

private fun collectSignatures(effect: EdgeEffect, condition: EdgeCondition): List<MethodSignature> {
    val signatures = mutableListOf<MethodSignature>()
    effect.assignMetaVar.values.flatten().forEach {
        check(!it.negated) { "Negated effect" }
        signatures += it.predicate.signature
    }
    condition.readMetaVar.values.flatten().forEach { if (!it.negated) signatures += it.predicate.signature }
    condition.other.forEach { if (!it.negated) signatures += it.predicate.signature }
    return signatures
}

private fun PythonTaintRuleGenerationCtx.evaluatePythonFormulaSignature(
    signatures: List<MethodSignature>,
    trace: SemgrepRuleLoadStepTrace,
): List<PythonRuleConditionBuilder> {
    val signature = signatures.first()
    if (signatures.any { it != signature }) TODO("Signature mismatch")
    if (signature.isGeneratedAnyValueGenerator()) TODO("Eliminate generated method")
    if (signature.isGeneratedStringConcat()) TODO("Eliminate generated string concat")

    // The function target already encodes the method/class; return type and signature predicate
    // conditions (IsType / class-name matches) are not representable in Python conditions.
    return evaluatePythonFunctionNames(signature.methodName.name, signature.enclosingClassName.name, trace)
        .map { name -> PythonRuleConditionBuilder().also { it.function = name } }
}

private fun PythonTaintRuleGenerationCtx.evaluatePythonEdgePredicateConstraint(
    edgeState: State,
    constraint: MethodConstraint?,
    negated: Boolean,
    conditions: MutableList<SerializedPythonCondition>,
    trace: SemgrepRuleLoadStepTrace,
) {
    if (!negated) {
        evaluatePythonMethodConstraints(edgeState, constraint, conditions, trace)
    } else {
        val negatedConditions = mutableListOf<SerializedPythonCondition>()
        evaluatePythonMethodConstraints(edgeState, constraint, negatedConditions, trace)
        val body = pythonAnd(negatedConditions)
        // Negating an empty (unrepresentable) body yields Not(true) = false, a never-firing rule.
        // Surface it rather than silently dropping the predicate's effect.
        if (body == PYTHON_TRUE) {
            trace.error(FailedToCreateTaintRules("Negated predicate has no Python condition representation"))
        }
        conditions += SerializedPythonCondition.Not(body)
    }
}

private fun PythonTaintRuleGenerationCtx.evaluatePythonMethodConstraints(
    edgeState: State,
    constraint: MethodConstraint?,
    conditions: MutableList<SerializedPythonCondition>,
    trace: SemgrepRuleLoadStepTrace,
) {
    when (constraint) {
        null -> {}
        is ParamConstraint -> {
            val cond = evaluatePythonParamCondition(edgeState, constraint.position.toAbstractPosition(), constraint, trace)
            if (cond != PYTHON_TRUE) conditions += cond
        }
        is NumberOfArgsConstraint -> conditions += SerializedPythonCondition.NumberOfArgs(constraint.num) // TODO kw-args are not supported
        // Class/method modifier (annotation) predicates have no Python mark-condition form.
        is ClassModifierConstraint,
        is MethodModifierConstraint -> {}
    }
}

private fun PythonTaintRuleGenerationCtx.evaluatePythonParamCondition(
    edgeState: State,
    position: PositionBase,
    param: ParamConstraint,
    trace: SemgrepRuleLoadStepTrace,
): SerializedPythonCondition = when (val condition = param.condition) {
    is IsMetavar -> {
        if (metaVarInfo.constraints[condition.metavar.toString()] != null) {
            trace.error(IgnoredMetavarConstraint(condition.metavar))
        }
        containsMarkWithAnyStateBefore(edgeState, condition.metavar, position.baseOnly())
    }
    // `$X = "..."` etc. — the argument must be a specific constant literal.
    is SpecificStringValue -> mkConstantCmp(position, SerializedPythonCondition.ConstantType.Str, condition.value)
    is SpecificIntValue -> mkConstantCmp(position, SerializedPythonCondition.ConstantType.Int, condition.value.toString())
    is SpecificBoolValue -> mkConstantCmp(position, SerializedPythonCondition.ConstantType.Bool, condition.value.toString())
    // Any string literal — the argument must be a string constant (mirrors Go's `ConstantMatches(".*")`).
    // `(?s)` so the match also covers multi-line string literals (`.` skips `\n` otherwise).
    ParamCondition.AnyStringLiteral ->
        SerializedPythonCondition.ConstantMatches(position.baseOnly().toPythonPosition(), "(?s).*")

    // Type / string-metavar / static-field / annotation / null predicates have no Python representation yet.
    is ParamCondition.TypeIs,
    is ParamCondition.StringValueMetaVar,
    is ParamCondition.ParamModifier,
    is ParamCondition.SpecificStaticFieldValue,
    SpecificNullValue -> PYTHON_TRUE
}

private fun mkConstantCmp(
    position: PositionBase,
    type: SerializedPythonCondition.ConstantType,
    value: String,
): SerializedPythonCondition.ConstantCmp = SerializedPythonCondition.ConstantCmp(
    pos = position.baseOnly().toPythonPosition(),
    value = SerializedPythonCondition.ConstantValue(type, value),
    cmp = SerializedPythonCondition.ConstantCmpType.Eq,
)

private fun findPythonMetaVarPosition(
    constraint: MethodConstraint?,
    varPositions: MutableMap<MetavarAtom, PythonRegisterVarPosition>,
) {
    if (constraint !is ParamConstraint) return
    val condition = constraint.condition
    if (condition !is IsMetavar) return
    val position = constraint.position.toAbstractPosition()
    varPositions.getOrPut(condition.metavar) { PythonRegisterVarPosition(condition.metavar, hashSetOf()) }
        .positions.add(position)
}

private fun Position.toAbstractPosition(): PositionBase = when (this) {
    is Position.Argument -> when (val idx = index) {
        is Position.ArgumentIndex.Any -> PositionBase.AnyArgument(idx.paramClassifier)
        is Position.ArgumentIndex.Concrete -> PositionBase.Argument(idx.idx)
    }
    is Position.Object -> PositionBase.This
    is Position.Result -> PositionBase.Result
}

private fun PositionBase.baseOnly(): PositionBaseWithModifiers.BaseOnly = PositionBaseWithModifiers.BaseOnly(this)
