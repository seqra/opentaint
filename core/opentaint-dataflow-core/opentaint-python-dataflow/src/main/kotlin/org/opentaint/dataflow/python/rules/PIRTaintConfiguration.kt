package org.opentaint.dataflow.python.rules

import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.python.AllArguments
import org.opentaint.dataflow.configuration.python.Argument
import org.opentaint.dataflow.configuration.python.ClassRef
import org.opentaint.dataflow.configuration.python.Condition
import org.opentaint.dataflow.configuration.python.KwArgument
import org.opentaint.dataflow.configuration.python.Position
import org.opentaint.dataflow.configuration.python.PositionAccessor
import org.opentaint.dataflow.configuration.python.PositionWithAccess
import org.opentaint.dataflow.configuration.python.Result
import org.opentaint.dataflow.configuration.python.Signature
import org.opentaint.dataflow.configuration.python.TaintAssignAction
import org.opentaint.dataflow.configuration.python.TaintCleanAction
import org.opentaint.dataflow.configuration.python.TaintCleaner
import org.opentaint.dataflow.configuration.python.TaintEntryPointSource
import org.opentaint.dataflow.configuration.python.TaintMark
import org.opentaint.dataflow.configuration.python.TaintPassAction
import org.opentaint.dataflow.configuration.python.TaintPassThrough
import org.opentaint.dataflow.configuration.python.TaintSink
import org.opentaint.dataflow.configuration.python.TaintSinkMeta
import org.opentaint.dataflow.configuration.python.TaintSource
import org.opentaint.dataflow.configuration.python.Target
import org.opentaint.dataflow.configuration.python.This
import org.opentaint.dataflow.configuration.python.TypeMatcher
import org.opentaint.dataflow.configuration.python.serialized.PythonPosition
import org.opentaint.dataflow.configuration.python.serialized.PythonPositionBase
import org.opentaint.dataflow.configuration.python.serialized.PythonPositionModifier
import org.opentaint.dataflow.configuration.python.serialized.PythonTarget
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCleaner
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCondition
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonEntryPointSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonPassThrough
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSignatureMatcher
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSink
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintAssignAction
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintCleanAction
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintConfig
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintPassAction

/**
 * Transforms a [SerializedPythonTaintConfig] (YAML model) into the in-memory
 * rule representation. The result carries no references to serialized types:
 *
 *  - Marks are interned into [TaintMark] instances.
 *  - Targets are converted into the local [Target] sealed hierarchy.
 *  - Positions are converted into the local [Position] model, where
 *    `Argument(idx = null)` is rewritten to [AllArguments] and a flat
 *    modifier list is folded into a right-leaning [PositionWithAccess] chain.
 *  - Conditions are converted into the local [Condition] AST. Per-action
 *    structural scopes (`decoratedWith`, `baseClass`) and the function
 *    target's `signature:` are *lifted* into the rule's [Condition], so
 *    actions are plain (mark, position) pairs and targets are name-only.
 *    Source and entry-point rules whose `taint:` list mixes multiple scopes
 *    are split into one in-memory rule per scope group.
 *  - Sink ids are synthesized from the rule's target and a default sink
 *    severity is supplied when meta is absent.
 *
 * Rules are exposed as flat lists. Callers dispatch on the rule's `target`
 * field — there is intentionally no indexing here, only what the shipped
 * Python config currently needs.
 */
class PIRTaintConfiguration(config: SerializedPythonTaintConfig) {

    private val marks = HashMap<String, TaintMark>()

    val entryPoints: List<TaintEntryPointSource> = config.entryPoint.flatMap(::convertEntryPoint)

    val sources: List<TaintSource> = config.source.flatMap(::convertSource)

    val sinks: List<TaintSink> = config.sink.map(::convertSink)

    val passThrough: List<TaintPassThrough> = config.passThrough.map(::convertPassThrough)

    val cleaners: List<TaintCleaner> = config.cleaner.map(::convertCleaner)

    private fun convertEntryPoint(rule: SerializedPythonEntryPointSource): List<TaintEntryPointSource> {
        val baseCondition = combineConditions(convertCondition(rule.condition), signatureCondition(rule.target))
        val target = convertTarget(rule.target)
        return groupByScope(rule.taint).map { (scope, actions) ->
            TaintEntryPointSource(
                target = target,
                condition = combineWithScope(baseCondition, scope),
                taint = actions.map(::convertAssignAction),
            )
        }
    }

    private fun convertSource(rule: SerializedPythonSource): List<TaintSource> {
        val baseCondition = combineConditions(convertCondition(rule.condition), signatureCondition(rule.target))
        val target = convertTarget(rule.target)
        return groupByScope(rule.taint).map { (scope, actions) ->
            TaintSource(
                target = target,
                condition = combineWithScope(baseCondition, scope),
                taint = actions.map(::convertAssignAction),
            )
        }
    }

    private fun convertSink(rule: SerializedPythonSink): TaintSink = TaintSink(
        target = convertTarget(rule.target),
        condition = combineConditions(convertCondition(rule.condition), signatureCondition(rule.target)),
        id = sinkId(rule.target),
        meta = sinkMeta(rule),
    )

    private fun convertPassThrough(rule: SerializedPythonPassThrough): TaintPassThrough = TaintPassThrough(
        target = convertTarget(rule.target),
        condition = combineConditions(convertCondition(rule.condition), signatureCondition(rule.target)),
        copy = rule.copy.map(::convertPassAction),
    )

    private fun convertCleaner(rule: SerializedPythonCleaner): TaintCleaner = TaintCleaner(
        target = convertTarget(rule.target),
        condition = combineConditions(convertCondition(rule.condition), signatureCondition(rule.target)),
        cleans = rule.cleans.map(::convertCleanAction),
        forCategory = rule.`for`,
    )

    // region Mark + action conversion

    private fun mark(name: String): TaintMark = marks.getOrPut(name) { TaintMark(name) }

    private fun convertAssignAction(a: SerializedPythonTaintAssignAction): TaintAssignAction =
        TaintAssignAction(mark = mark(a.kind), pos = convertPosition(a.pos))

    private fun convertCleanAction(a: SerializedPythonTaintCleanAction): TaintCleanAction =
        TaintCleanAction(mark = a.taintKind?.let(::mark), pos = convertPosition(a.pos))

    private fun convertPassAction(a: SerializedPythonTaintPassAction): TaintPassAction =
        TaintPassAction(
            mark = a.taintKind?.let(::mark),
            from = convertPosition(a.from),
            to = convertPosition(a.to),
        )

    // endregion

    // region Target + signature

    private fun convertTarget(target: PythonTarget): Target = when (target) {
        is PythonTarget.Function -> Target.Function(target.function)
        is PythonTarget.Attribute -> Target.Attribute(target.attribute)
    }

    private fun signatureCondition(target: PythonTarget): Condition? =
        (target as? PythonTarget.Function)?.signature?.let {
            Condition.SignatureMatches(convertSignature(it))
        }

    private fun convertSignature(s: SerializedPythonSignatureMatcher): Signature = Signature(
        args = s.args.map(::convertTypeMatcher),
        returnType = convertTypeMatcher(s.`return`),
    )

    private fun convertTypeMatcher(s: String): TypeMatcher =
        if (s == "*") TypeMatcher.AnyType else TypeMatcher.Exact(s)

    // endregion

    // region Scope grouping

    /** (decoratedWith, baseClass) scope as it appears on a serialized assign action. */
    private data class Scope(val decoratedWith: String?, val baseClass: String?)

    private fun groupByScope(
        actions: List<SerializedPythonTaintAssignAction>,
    ): Map<Scope, List<SerializedPythonTaintAssignAction>> =
        actions.groupBy { Scope(it.decoratedWith, it.baseClass) }

    private fun combineWithScope(base: Condition, scope: Scope): Condition {
        val parts = buildList {
            if (base !is Condition.ConstantTrue) add(base)
            scope.decoratedWith?.let { add(Condition.DecoratedWith(it)) }
            scope.baseClass?.let { add(Condition.BaseClass(it)) }
        }
        return collapseAnd(parts)
    }

    private fun combineConditions(base: Condition, extra: Condition?): Condition {
        if (extra == null) return base
        val parts = buildList {
            if (base !is Condition.ConstantTrue) add(base)
            add(extra)
        }
        return collapseAnd(parts)
    }

    private fun collapseAnd(parts: List<Condition>): Condition = when (parts.size) {
        0 -> Condition.ConstantTrue
        1 -> parts.single()
        else -> Condition.And(parts)
    }

    // endregion

    // region Position + condition conversion

    private fun convertPosition(p: PythonPosition): Position = when (p) {
        is PythonPosition.BaseOnly -> convertBase(p.base)
        is PythonPosition.WithModifiers -> p.modifiers.fold(convertBase(p.base)) { acc, mod ->
            PositionWithAccess(acc, convertAccessor(mod))
        }
    }

    private fun convertBase(base: PythonPositionBase): Position = when (base) {
        is PythonPositionBase.Argument -> base.idx?.let(::Argument) ?: AllArguments
        is PythonPositionBase.KwArgument -> KwArgument(base.name)
        PythonPositionBase.This -> This
        PythonPositionBase.Result -> Result
        is PythonPositionBase.ClassRef -> ClassRef(base.fqn)
    }

    private fun convertAccessor(m: PythonPositionModifier): PositionAccessor = when (m) {
        PythonPositionModifier.ArrayElement -> PositionAccessor.ElementAccessor
        is PythonPositionModifier.Field -> PositionAccessor.FieldAccessor(m.name)
    }

    private fun convertCondition(c: SerializedPythonCondition?): Condition = when (c) {
        null -> Condition.ConstantTrue
        is SerializedPythonCondition.Or -> Condition.Or(c.anyOf.map(::convertCondition))
        is SerializedPythonCondition.And -> Condition.And(c.allOf.map(::convertCondition))
        is SerializedPythonCondition.Not -> Condition.Not(convertCondition(c.not))
        is SerializedPythonCondition.ContainsMark -> Condition.ContainsMark(
            mark = mark(c.tainted),
            pos = convertPosition(c.pos),
        )
    }

    // endregion

    private fun sinkId(target: PythonTarget): String = when (target) {
        is PythonTarget.Function -> "function:${target.function}"
        is PythonTarget.Attribute -> "attribute:${target.attribute}"
    }

    private fun sinkMeta(rule: SerializedPythonSink): TaintSinkMeta = TaintSinkMeta(
        message = rule.meta?.note ?: DEFAULT_SINK_MESSAGE,
        severity = CommonTaintConfigurationSinkMeta.Severity.Warning,
        cwe = rule.meta?.cwe,
        note = rule.meta?.note,
    )

    companion object {
        private const val DEFAULT_SINK_MESSAGE = "taint reaches sink"
    }
}
