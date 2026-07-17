package org.opentaint.semgrep.pattern.conversion.python

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.dataflow.configuration.python.serialized.PythonPosition
import org.opentaint.dataflow.configuration.python.serialized.PythonPositionBase
import org.opentaint.dataflow.configuration.python.serialized.PythonSinkMetaData
import org.opentaint.dataflow.configuration.python.serialized.PythonTarget
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCleaner
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCondition
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonEntryPointSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonExitSink
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonRule
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSink
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintAssignAction
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintCleanAction
import org.opentaint.semgrep.pattern.FailedToCreateTaintRules
import org.opentaint.semgrep.pattern.IgnoredClassConstraint
import org.opentaint.semgrep.pattern.IgnoredDecoratorArguments
import org.opentaint.semgrep.pattern.IgnoredMetavarConstraint
import org.opentaint.semgrep.pattern.NonMethodCallCleaner
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.conversion.IsMetavar
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.ParamCondition
import org.opentaint.semgrep.pattern.conversion.PythonConcreteType
import org.opentaint.semgrep.pattern.conversion.PythonLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureModifier
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureModifierValue
import org.opentaint.semgrep.pattern.conversion.SpecificBoolValue
import org.opentaint.semgrep.pattern.conversion.SpecificIntValue
import org.opentaint.semgrep.pattern.conversion.SpecificNullValue
import org.opentaint.semgrep.pattern.conversion.SpecificStringValue
import org.opentaint.semgrep.pattern.conversion.TypeConstraint
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
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.MethodPredicate
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

            val target = pythonTargetFor(condition.ruleCondition.function)
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
                    target = pythonTargetFor(condition.ruleCondition.function),
                    condition = condition.ruleCondition.condition.nullIfTrue(),
                    meta = ctx.meta.toPythonSinkMeta(),
                )

                TaintRuleEdge.Kind.MethodExit -> rules += SerializedPythonExitSink(
                    target = PythonTarget.Function(ANY_PYTHON_FUNCTION),
                    condition = condition.ruleCondition.condition.rewriteAsEndCondition().nullIfTrue(),
                    meta = ctx.meta.toPythonSinkMeta(),
                )

                TaintRuleEdge.Kind.MethodEnter ->
                    ctx.trace.error(FailedToCreateTaintRules("Method-enter sinks are not supported yet"))
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
                    target = pythonTargetFor(condition.ruleCondition.function),
                    condition = condition.ruleCondition.condition.nullIfTrue(),
                    cleans = actions,
                    info = edgeRuleInfo(ruleEdge).toPython(),
                )
            }
        }
    }

    return rules
}

// The converter encodes an attribute read as a synthetic method name carrying
// PythonLanguageStrategy.ATTR_READ_AUX_FN_PREFIX; recover the attribute target from it.
private fun pythonTargetFor(function: String): PythonTarget =
    PythonLanguageStrategy.attrReadAttrOrNull(function)
        ?.let { PythonTarget.Attribute(it) }
        ?: PythonTarget.Function(function)

private fun SinkMetaData.toPythonSinkMeta(): PythonSinkMetaData = PythonSinkMetaData(cwe = cwe, note = note)

private fun PythonTaintRuleGenerationCtx.buildPythonStateAssignActions(
    stateAfter: State,
    edgeCondition: PythonEvaluatedEdgeCondition,
): List<SerializedPythonTaintAssignAction> {
    val result = stateAfter.register.assignedVars.keys.flatMapTo(mutableListOf()) { varName ->
        val varPosition = edgeCondition.accessedVarPosition[varName] ?: return@flatMapTo emptyList()
        varPosition.positions.flatMap { stateAssignMark(varPosition.varName, stateAfter, it) }
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
        varPosition.positions.flatMap { stateCleanMark(varPosition.varName, stateAfter, stateBefore, it) }
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
                stateChecks += ctx.containsStateMark(metaVar, stateOfEdge, pos)
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
    // A subscript read attaches a field-signature modifier to the Result position; strip it into
    // element accessors and re-attach it to the Result position wherever it is materialized.
    val resultFieldChains = mutableListOf<String>()
    val normalizedCondition = condition.dropFieldResultModifier(resultFieldChains)
    val normalizedEffect = effect.dropFieldResultModifier(resultFieldChains)
    val resultModifiers = resultModifiersOf(resultFieldChains)

    val builders = evaluatePythonFormulaSignature(collectSignatures(normalizedEffect, normalizedCondition), trace)

    return builders.map { builder ->
        normalizedCondition.readMetaVar.values.flatten().forEach {
            evaluatePythonEdgePredicateConstraint(edgeState, it.predicate.constraint, it.negated, resultModifiers, builder.conditions, trace)
        }
        normalizedCondition.other.forEach {
            evaluatePythonEdgePredicateConstraint(edgeState, it.predicate.constraint, it.negated, resultModifiers, builder.conditions, trace)
        }

        val varPositions = hashMapOf<MetavarAtom, PythonRegisterVarPosition>()
        normalizedEffect.assignMetaVar.values.flatten().forEach {
            findPythonMetaVarPosition(it.predicate.constraint, resultModifiers, varPositions)
        }

        PythonEvaluatedEdgeCondition(builder.build(), varPositions)
    }
}

private fun EdgeEffect.dropFieldResultModifier(fieldChains: MutableList<String>) =
    EdgeEffect(assignMetaVar.dropFieldResultModifier(fieldChains))

private fun EdgeCondition.dropFieldResultModifier(fieldChains: MutableList<String>) =
    EdgeCondition(readMetaVar.dropFieldResultModifier(fieldChains), other.dropFieldResultModifier(fieldChains))

private fun Map<MetavarAtom, List<MethodPredicate>>.dropFieldResultModifier(fieldChains: MutableList<String>) =
    mapValues { (_, v) -> v.dropFieldResultModifier(fieldChains) }

private fun List<MethodPredicate>.dropFieldResultModifier(fieldChains: MutableList<String>): List<MethodPredicate> =
    mapNotNull { it.dropFieldResultModifier(fieldChains) }

private fun MethodPredicate.dropFieldResultModifier(fieldChains: MutableList<String>): MethodPredicate? {
    val constraint = predicate.constraint as? ParamConstraint ?: return this
    val paramModifier = constraint.condition as? ParamCondition.ParamModifier ?: return this
    val remainingModifier = paramModifier.dropFieldResultModifier { field ->
        fieldChains += field
        check(constraint.position is Position.Result) { "Field modifier on non-result position" }
        check(!negated) { "Negated field modifier" }
    }
    return if (remainingModifier != null) this else null
}

/** Splits the collected field chain into serialized element accessors (single chain, mirrors Go). */
private fun resultModifiersOf(resultFieldChains: List<String>): List<PositionModifier>? {
    if (resultFieldChains.isEmpty()) return null
    val uniqueChains = resultFieldChains.distinct()
    check(uniqueChains.size == 1) { "Multiple result field chains" }
    return PythonLanguageStrategy.splitFieldNames(uniqueChains.single()).map {
        when (it) {
            PythonLanguageStrategy.INDEX_AUX_FIELD_NAME -> PositionModifier.ArrayElement
            else -> PositionModifier.Field("", it, "")
        }
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
    resultModifiers: List<PositionModifier>?,
    conditions: MutableList<SerializedPythonCondition>,
    trace: SemgrepRuleLoadStepTrace,
) {
    if (!negated) {
        evaluatePythonMethodConstraints(edgeState, constraint, resultModifiers, conditions, trace)
    } else {
        val negatedConditions = mutableListOf<SerializedPythonCondition>()
        evaluatePythonMethodConstraints(edgeState, constraint, resultModifiers, negatedConditions, trace)
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
    resultModifiers: List<PositionModifier>?,
    conditions: MutableList<SerializedPythonCondition>,
    trace: SemgrepRuleLoadStepTrace,
) {
    when (constraint) {
        null -> {}
        is ParamConstraint -> {
            val cond = evaluatePythonParamCondition(
                edgeState, constraint.position.toPositionWithModifiers(resultModifiers), constraint, trace,
            )
            if (cond != PYTHON_TRUE) conditions += cond
        }
        is NumberOfArgsConstraint -> conditions += SerializedPythonCondition.NumberOfArgs(constraint.num) // TODO kw-args are not supported
        is MethodModifierConstraint -> conditions += pythonDecoratorCondition(constraint.modifier, trace)

        // TODO
        is ClassModifierConstraint -> trace.error(IgnoredClassConstraint())
    }
}

/**
 * Gates the rule on the decorator a `@dec def f(...)` pattern requires, named as the pattern writes
 * it (`entry_point`, `app.route`). An unresolvable name (`@$DEC`) yields a never-matching rule rather
 * than an ungated one: dropping the gate would make `@dec def f($P)` taint the parameter of *every*
 * function. Decorator arguments (`@app.route("/p")`) have no condition form, so the name alone
 * matches and the rule widens to every use of the decorator instead of being dropped.
 */
private fun pythonDecoratorCondition(
    modifier: SignatureModifier,
    trace: SemgrepRuleLoadStepTrace,
): SerializedPythonCondition {
    val name = ((modifier.type as? TypeConstraint.Concrete)?.type as? PythonConcreteType.Named)?.name

    if (name == null) {
        trace.error(FailedToCreateTaintRules("Decorator name is not concrete and cannot be scoped"))
        return PYTHON_FALSE
    }

    if (modifier.value !is SignatureModifierValue.NoValue && modifier.value !is SignatureModifierValue.AnyValue) {
        trace.error(IgnoredDecoratorArguments(name))
    }
    return SerializedPythonCondition.MethodDecorated(name)
}

private fun PythonTaintRuleGenerationCtx.evaluatePythonParamCondition(
    edgeState: State,
    position: PositionBaseWithModifiers,
    param: ParamConstraint,
    trace: SemgrepRuleLoadStepTrace,
): SerializedPythonCondition = when (val condition = param.condition) {
    is IsMetavar -> {
        if (metaVarInfo.constraints[condition.metavar.toString()] != null) {
            trace.error(IgnoredMetavarConstraint(condition.metavar))
        }
        containsMarkWithAnyStateBefore(edgeState, condition.metavar, position)
    }
    // `$X = "..."` etc. — the argument must be a specific constant literal.
    is SpecificStringValue -> mkConstantCmp(position, SerializedPythonCondition.ConstantType.Str, condition.value)
    is SpecificIntValue -> mkConstantCmp(position, SerializedPythonCondition.ConstantType.Int, condition.value.toString())
    is SpecificBoolValue -> mkConstantCmp(position, SerializedPythonCondition.ConstantType.Bool, condition.value.toString())
    // Any string literal — the argument must be a string constant (mirrors Go's `ConstantMatches(".*")`).
    // `(?s)` so the match also covers multi-line string literals (`.` skips `\n` otherwise).
    ParamCondition.AnyStringLiteral ->
        SerializedPythonCondition.ConstantMatches(position.toPythonPosition(), "(?s).*")

    // Type / string-metavar / static-field / annotation / null predicates have no Python representation yet.
    // A ParamModifier is stripped upstream (dropFieldResultModifier); reaching it here means the modifier
    // sat on a non-result position and could not be materialized as an accessor.
    is ParamCondition.TypeIs,
    is ParamCondition.StringValueMetaVar,
    is ParamCondition.ParamModifier,
    is ParamCondition.SpecificStaticFieldValue,
    SpecificNullValue -> PYTHON_TRUE
}

private fun mkConstantCmp(
    position: PositionBaseWithModifiers,
    type: SerializedPythonCondition.ConstantType,
    value: String,
): SerializedPythonCondition.ConstantCmp = SerializedPythonCondition.ConstantCmp(
    pos = position.toPythonPosition(),
    value = SerializedPythonCondition.ConstantValue(type, value),
    cmp = SerializedPythonCondition.ConstantCmpType.Eq,
)

private fun findPythonMetaVarPosition(
    constraint: MethodConstraint?,
    resultModifiers: List<PositionModifier>?,
    varPositions: MutableMap<MetavarAtom, PythonRegisterVarPosition>,
) {
    if (constraint !is ParamConstraint) return
    val condition = constraint.condition
    if (condition !is IsMetavar) return
    val position = constraint.position.toPositionWithModifiers(resultModifiers)
    varPositions.getOrPut(condition.metavar) { PythonRegisterVarPosition(condition.metavar, hashSetOf()) }
        .positions.add(position)
}

private fun Position.toPositionWithModifiers(resultModifiers: List<PositionModifier>?): PositionBaseWithModifiers {
    val base = toAbstractPosition()
    return if (this is Position.Result && resultModifiers != null) {
        PositionBaseWithModifiers.WithModifiers(base, resultModifiers)
    } else {
        PositionBaseWithModifiers.BaseOnly(base)
    }
}

private fun Position.toAbstractPosition(): PositionBase = when (this) {
    is Position.Argument -> when (val idx = index) {
        is Position.ArgumentIndex.Any -> PositionBase.AnyArgument(idx.paramClassifier)
        is Position.ArgumentIndex.Concrete -> PositionBase.Argument(idx.idx)
    }
    is Position.Object -> PositionBase.This
    is Position.Result -> PositionBase.Result
}

private fun SerializedPythonCondition.rewriteAsEndCondition(): SerializedPythonCondition = when (this) {
    is SerializedPythonCondition.And -> SerializedPythonCondition.And(allOf.map { it.rewriteAsEndCondition() })
    is SerializedPythonCondition.Or -> SerializedPythonCondition.Or(anyOf.map { it.rewriteAsEndCondition() })
    is SerializedPythonCondition.Not -> SerializedPythonCondition.Not(not.rewriteAsEndCondition())
    is SerializedPythonCondition.ContainsMark -> copy(pos = pos.rewriteAsEndPosition())
    is SerializedPythonCondition.ContainsMarkOnAnyAccessor -> copy(pos = pos.rewriteAsEndPosition())
    is SerializedPythonCondition.ConstantCmp -> copy(pos = pos.rewriteAsEndPosition())
    is SerializedPythonCondition.ConstantMatches -> copy(pos = pos.rewriteAsEndPosition())
    // Call arity is meaningless at method exit.
    is SerializedPythonCondition.NumberOfArgs -> PYTHON_TRUE
    // Predicates of the enclosing function itself: no position to rewrite, and they still hold at exit.
    is SerializedPythonCondition.MethodDecorated,
    is SerializedPythonCondition.ClassExtends -> this
}

private fun PythonPosition.rewriteAsEndPosition(): PythonPosition = when (this) {
    is PythonPosition.BaseOnly -> PythonPosition.BaseOnly(base.rewriteAsEndPosition())
    is PythonPosition.WithModifiers -> PythonPosition.WithModifiers(base.rewriteAsEndPosition(), modifiers)
}

private fun PythonPositionBase.rewriteAsEndPosition(): PythonPositionBase = when (this) {
    is PythonPositionBase.Argument -> PythonPositionBase.Result
    is PythonPositionBase.KwArgument -> PythonPositionBase.Result
    PythonPositionBase.This -> this
    PythonPositionBase.Result -> this
    is PythonPositionBase.ClassRef -> this
}
