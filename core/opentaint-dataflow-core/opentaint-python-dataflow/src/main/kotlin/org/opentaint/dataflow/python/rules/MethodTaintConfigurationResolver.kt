package org.opentaint.dataflow.python.rules

import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.configuration.python.AllArguments
import org.opentaint.dataflow.configuration.python.Argument
import org.opentaint.dataflow.configuration.python.ClassRef
import org.opentaint.dataflow.configuration.python.ContainsMark
import org.opentaint.dataflow.configuration.python.KwArgument
import org.opentaint.dataflow.configuration.python.PIRCondition
import org.opentaint.dataflow.configuration.python.Position
import org.opentaint.dataflow.configuration.python.PositionAccessor
import org.opentaint.dataflow.configuration.python.PositionWithAccess
import org.opentaint.dataflow.configuration.python.Result
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
import org.opentaint.dataflow.configuration.python.serialized.PythonPosition
import org.opentaint.dataflow.configuration.python.serialized.PythonPositionBase
import org.opentaint.dataflow.configuration.python.serialized.PythonPositionModifier
import org.opentaint.dataflow.configuration.python.serialized.PythonTarget
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCleaner
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCondition
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonEntryPointSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonPassThrough
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonRule
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSignatureMatcher
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSink
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSourceRule
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintAssignAction
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintCleanAction
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintPassAction
import org.opentaint.dataflow.python.graph.PIRSimpleNameUnknownFunction
import org.opentaint.ir.api.python.PIRClassType
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRParameter
import org.opentaint.ir.api.python.PIRType
import org.opentaint.ir.api.python.PythonNames

/**
 * Compiles serialized Python taint rules against a concrete
 * [PIRFunction] (or an attribute name). Mirrors the JVM
 * `MethodTaintConfigurationResolver` — name matching, signature
 * matching and structural scope predicates (`decoratedWith`,
 * `baseClass`) are resolved here against the matched method and used
 * to drop non-matching rules / scope groups, so the runtime
 * [Condition] AST attached to compiled rules carries only value-level
 * predicates (`ConstantTrue | Not | And | Or | ContainsMark`).
 */
internal object MethodTaintConfigurationResolver {

    // region Function-targeted resolution

    fun resolveEntryPoints(
        serialized: List<SerializedPythonEntryPointSource>,
        method: PIRFunction,
    ): List<TaintEntryPointSource> = resolveSourceRule(serialized, method) { condition, actions ->
        TaintEntryPointSource(Target.Function(method), condition, actions)
    }

    fun resolveSources(
        serialized: List<SerializedPythonSource>,
        method: PIRFunction,
    ): List<TaintSource> = resolveSourceRule(serialized, method) { condition, actions ->
        TaintSource(Target.Function(method), condition, actions)
    }

    fun resolveSinks(
        serialized: List<SerializedPythonSink>,
        method: PIRFunction,
    ): List<TaintSink> = resolveFunctionTargeted(serialized, method) { rule, fn ->
        TaintSink(
            target = Target.Function(method),
            condition = convertCondition(rule.condition),
            id = "function:${fn.function}",
            meta = sinkMeta(rule),
        )
    }

    fun resolvePassThrough(
        serialized: List<SerializedPythonPassThrough>,
        method: PIRFunction,
    ): List<TaintPassThrough> = resolveFunctionTargeted(serialized, method) { rule, _ ->
        TaintPassThrough(
            target = Target.Function(method),
            condition = convertCondition(rule.condition),
            copy = rule.copy.map(::convertPassAction),
        )
    }

    fun resolveCleaners(
        serialized: List<SerializedPythonCleaner>,
        method: PIRFunction,
    ): List<TaintCleaner> = resolveFunctionTargeted(serialized, method) { rule, _ ->
        TaintCleaner(
            target = Target.Function(method),
            condition = convertCondition(rule.condition),
            cleans = rule.cleans.map(::convertCleanAction),
            forCategory = rule.`for`,
        )
    }

    // endregion

    // region Attribute-targeted resolution

    fun resolveAttributeSources(
        serialized: List<SerializedPythonSource>,
        name: String,
    ): List<TaintSource> = resolveAttributeTargeted(serialized, name) { rule ->
        rule.taint.forEach { it.requireNoMethodScope(name) }
        TaintSource(
            target = Target.Attribute(name),
            condition = convertCondition(rule.condition),
            taint = rule.taint.map(::convertAssignAction),
        )
    }

    fun resolveAttributeSinks(
        serialized: List<SerializedPythonSink>,
        name: String,
    ): List<TaintSink> = resolveAttributeTargeted(serialized, name) { rule ->
        TaintSink(
            target = Target.Attribute(name),
            condition = convertCondition(rule.condition),
            id = "attribute:$name",
            meta = sinkMeta(rule),
        )
    }

    fun resolveAttributePassThrough(
        serialized: List<SerializedPythonPassThrough>,
        name: String,
    ): List<TaintPassThrough> = resolveAttributeTargeted(serialized, name) { rule ->
        TaintPassThrough(
            target = Target.Attribute(name),
            condition = convertCondition(rule.condition),
            copy = rule.copy.map(::convertPassAction),
        )
    }

    fun resolveAttributeCleaners(
        serialized: List<SerializedPythonCleaner>,
        name: String,
    ): List<TaintCleaner> = resolveAttributeTargeted(serialized, name) { rule ->
        TaintCleaner(
            target = Target.Attribute(name),
            condition = convertCondition(rule.condition),
            cleans = rule.cleans.map(::convertCleanAction),
            forCategory = rule.`for`,
        )
    }

    // endregion

    /**
     * Shared scaffolding for source / entry-point resolution: match the rule against [method],
     * split `taint:` actions by `(decoratedWith, baseClass)` scope, drop scope groups that fail,
     * and hand each surviving group to [build].
     */
    private inline fun <S : SerializedPythonSourceRule, T> resolveSourceRule(
        serialized: List<S>,
        method: PIRFunction,
        build: (PIRCondition, List<TaintAssignAction>) -> T,
    ): List<T> = serialized.flatMap { rule ->
        val fn = rule.target as? PythonTarget.Function ?: return@flatMap emptyList()
        if (!fn.matches(method)) return@flatMap emptyList()

        val baseCondition = convertCondition(rule.condition)
        rule.taint.groupBy { it.decoratedWith to it.baseClass }
            .mapNotNull { (scope, actions) ->
                val (decoratedWith, baseClass) = scope
                if (decoratedWith != null && !method.hasDecorator(decoratedWith)) return@mapNotNull null
                if (baseClass != null && !method.hasBaseClass(baseClass)) return@mapNotNull null
                build(baseCondition, actions.map(::convertAssignAction))
            }
    }

    /** Match a function-target rule (sinks / passthrough / cleaners) against [method]. */
    private inline fun <S : SerializedPythonRule, T> resolveFunctionTargeted(
        serialized: List<S>,
        method: PIRFunction,
        build: (S, PythonTarget.Function) -> T,
    ): List<T> = serialized.mapNotNull { rule ->
        val fn = rule.target as? PythonTarget.Function ?: return@mapNotNull null
        if (!fn.matches(method)) return@mapNotNull null
        build(rule, fn)
    }

    /** Match an attribute-target rule against the attribute [name]. */
    private inline fun <S : SerializedPythonRule, T> resolveAttributeTargeted(
        serialized: List<S>,
        name: String,
        build: (S) -> T,
    ): List<T> = serialized.mapNotNull { rule ->
        val attr = rule.target as? PythonTarget.Attribute ?: return@mapNotNull null
        if (attr.attribute != name) return@mapNotNull null
        build(rule)
    }

    // region Matching

    private fun PythonTarget.Function.matches(method: PIRFunction): Boolean {
        if (!matchesName(function, method)) return false
        signature?.let { if (!matchesSignature(it, method)) return false }
        return true
    }

    private fun matchesName(name: String, method: PIRFunction): Boolean {
        if (method is PIRSimpleNameUnknownFunction) return name.substringAfterLast('.') == method.name

        val qn = method.qualifiedName
        val ctorQn = if (method.enclosingClass != null) qn.removeSuffix(".${PythonNames.INIT_METHOD}") else qn
        return when {
            hasRegexMetaChar(name) -> {
                val rx = Regex(name)
                rx.matches(qn) || (ctorQn != qn && rx.matches(ctorQn))
            }
            '.' in name -> qn == name || ctorQn == name
            else -> method.name == name
        }
    }

    /** `.` is treated as a literal FQN separator, not a regex meta char. */
    private fun hasRegexMetaChar(name: String): Boolean = name.any { it in REGEX_META_CHARS }

    private fun matchesSignature(sig: SerializedPythonSignatureMatcher, method: PIRFunction): Boolean {
        val params = method.declaredParameters()
        if (params.size != sig.args.size) return false
        if (!matchesType(sig.`return`, method.returnType)) return false
        return params.zip(sig.args).all { (p, m) -> matchesType(m, p.type) }
    }

    /** Matches the serialized matcher token (`*` or an FQN) against a [PIRClassType]. */
    private fun matchesType(matcher: String, type: PIRType): Boolean =
        matcher == "*" || (type as? PIRClassType)?.qualifiedName == matcher

    /**
     * Parameters as the user wrote them — drops the implicit receiver slot
     * (`self` / `cls`) so signature matchers like `() *` line up with the
     * source-level arity. Uses `enclosingClass` + `isStaticMethod` rather
     * than parameter naming so misnamed receivers and top-level functions
     * both behave; `@classmethod`'s `cls` slot is dropped by the same rule
     * since `isClassMethod` implies `enclosingClass != null` and
     * `!isStaticMethod`.
     */
    private fun PIRFunction.declaredParameters(): List<PIRParameter> = when {
        enclosingClass == null || isStaticMethod -> parameters
        else -> if (parameters.isEmpty()) parameters else parameters.drop(1)
    }

    private fun PIRFunction.hasDecorator(fqn: String): Boolean =
        decorators.any { it.qualifiedName == fqn }

    private fun PIRFunction.hasBaseClass(fqn: String): Boolean =
        enclosingClass?.let { fqn in it.mro } == true

    // endregion

    // region Position + condition + action conversion

    private fun convertAssignAction(a: SerializedPythonTaintAssignAction): TaintAssignAction =
        TaintAssignAction(mark = TaintMark(a.kind), pos = convertPosition(a.pos))

    private fun convertCleanAction(a: SerializedPythonTaintCleanAction): TaintCleanAction =
        TaintCleanAction(mark = a.taintKind?.let(::TaintMark), pos = convertPosition(a.pos))

    private fun convertPassAction(a: SerializedPythonTaintPassAction): TaintPassAction =
        TaintPassAction(
            mark = a.taintKind?.let(::TaintMark),
            from = convertPosition(a.from),
            to = convertPosition(a.to),
        )

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

    private fun convertCondition(c: SerializedPythonCondition?): PIRCondition = when (c) {
        null -> mkTrue()
        is SerializedPythonCondition.Or -> CommonCondition.Or(c.anyOf.map(::convertCondition))
        is SerializedPythonCondition.And -> CommonCondition.And(c.allOf.map(::convertCondition))
        is SerializedPythonCondition.Not -> CommonCondition.Not(convertCondition(c.not))
        is SerializedPythonCondition.ContainsMark -> CommonCondition.Atom(ContainsMark(
            mark = TaintMark(c.tainted),
            pos = convertPosition(c.pos),
        ))
    }

    // endregion

    /**
     * Attribute rules cannot meaningfully scope by `decoratedWith` / `baseClass` — those
     * are properties of a function's enclosing class / decorators, neither of which an
     * attribute access has. Treat a non-null scope on an attribute action as a config bug.
     */
    private fun SerializedPythonTaintAssignAction.requireNoMethodScope(attributeName: String) {
        require(decoratedWith == null && baseClass == null) {
            "attribute rule '$attributeName' has a method-only scope " +
                "(decoratedWith=$decoratedWith, baseClass=$baseClass) on a taint action"
        }
    }

    private fun sinkMeta(rule: SerializedPythonSink): TaintSinkMeta = TaintSinkMeta(
        message = rule.meta?.note ?: DEFAULT_SINK_MESSAGE,
        severity = CommonTaintConfigurationSinkMeta.Severity.Warning,
        cwe = rule.meta?.cwe,
        note = rule.meta?.note,
    )

    private const val DEFAULT_SINK_MESSAGE = "taint reaches sink"
    private val REGEX_META_CHARS = setOf('*', '+', '?', '[', ']', '(', ')', '|', '^', '$', '\\', '{', '}')
}
