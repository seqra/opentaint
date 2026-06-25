package org.opentaint.dataflow.python.rules

import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.mkFalse
import org.opentaint.dataflow.configuration.mkOr
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.configuration.python.AllArguments
import org.opentaint.dataflow.configuration.python.Argument
import org.opentaint.dataflow.configuration.python.BoolConstantValue
import org.opentaint.dataflow.configuration.python.ClassRef
import org.opentaint.dataflow.configuration.python.ConstantCmp
import org.opentaint.dataflow.configuration.python.ConstantCmpType
import org.opentaint.dataflow.configuration.python.ConstantMatches
import org.opentaint.dataflow.configuration.python.ConstantValue
import org.opentaint.dataflow.configuration.python.ContainsMark
import org.opentaint.dataflow.configuration.python.IntConstantValue
import org.opentaint.dataflow.configuration.python.KwArgument
import org.opentaint.dataflow.configuration.python.PIRCondition
import org.opentaint.dataflow.configuration.python.Position
import org.opentaint.dataflow.configuration.python.PositionAccessor
import org.opentaint.dataflow.configuration.python.PositionWithAccess
import org.opentaint.dataflow.configuration.python.PythonRuleCondition
import org.opentaint.dataflow.configuration.python.Result
import org.opentaint.dataflow.configuration.python.StrConstantValue
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
import org.opentaint.dataflow.configuration.python.serialized.ItemInfo
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
import org.opentaint.dataflow.configuration.simplify
import org.opentaint.dataflow.python.graph.PIRSimpleNameUnknownFunction
import org.opentaint.dataflow.python.graph.PIRUnknownFunction
import org.opentaint.ir.api.python.PIRClassType
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRParameter
import org.opentaint.ir.api.python.PIRParameterKind
import org.opentaint.ir.api.python.PIRType
import org.opentaint.ir.api.python.PythonNames
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

/**
 * Compiles serialized Python taint rules against a single concrete
 * [PIRFunction] (function-targeted rules) or, when constructed via
 * [forAttribute], against an attribute name (attribute-targeted rules).
 * Mirrors the JVM `MethodTaintConfigurationResolver` — one instance per
 * matched method — name matching, signature matching and structural scope
 * predicates (`decoratedWith`, `baseClass`) are resolved here against the
 * matched method and used to drop non-matching rules / scope groups, so the
 * runtime [PIRCondition] AST attached to compiled rules carries only
 * value-level predicates (`ConstantTrue | Not | And | Or | ContainsMark |
 * ConstantCmp | ConstantMatches`). Arity (`NumberOfArgs`) is folded to a
 * constant against the signature here and never reaches the runtime AST; an
 * unknown callee carries a synthetic signature derived from its captured call
 * shape ([PIRUnknownFunction.callArgs]), so the same folding applies.
 *
 * [method] is null for attribute-targeted resolution (an attribute access has
 * no enclosing call, hence no positional arguments or call arity).
 */
internal class MethodTaintConfigurationResolver(private val method: PIRFunction?) {

    private val argIndices: List<Int> by lazy {
        when (val m = method) {
            is PIRUnknownFunction -> m.positionalArgIndices
            null -> emptyList()
            else -> m.argumentIndices()
        }
    }

    // region Function-targeted resolution

    fun resolveEntryPoints(
        serialized: List<SerializedPythonEntryPointSource>,
    ): List<TaintEntryPointSource> = resolveSourceRule(serialized) { condition, actions, method, info ->
        TaintEntryPointSource(Target.Function(method), condition, actions, info)
    }

    fun resolveSources(
        serialized: List<SerializedPythonSource>,
    ): List<TaintSource> = resolveSourceRule(serialized) { condition, actions, method, info ->
        TaintSource(Target.Function(method), condition, actions, info)
    }

    fun resolveSinks(
        serialized: List<SerializedPythonSink>,
    ): List<TaintSink> = resolveFunctionTargeted(serialized) { rule, fn, method ->
        TaintSink(
            target = Target.Function(method),
            condition = resolveCondition(rule.condition),
            id = "function:${fn.function}",
            meta = sinkMeta(rule),
        )
    }

    fun resolvePassThrough(
        serialized: List<SerializedPythonPassThrough>,
    ): List<TaintPassThrough> = resolveFunctionTargeted(serialized) { rule, _, method ->
        TaintPassThrough(
            target = Target.Function(method),
            condition = resolveCondition(rule.condition),
            copy = rule.copy.flatMap { convertPassActions(it) },
        )
    }

    fun resolveCleaners(
        serialized: List<SerializedPythonCleaner>,
    ): List<TaintCleaner> = resolveFunctionTargeted(serialized) { rule, _, method ->
        TaintCleaner(
            target = Target.Function(method),
            condition = resolveCondition(rule.condition),
            cleans = rule.cleans.flatMap { convertCleanActions(it) },
            forCategory = rule.`for`,
            info = rule.info,
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
            condition = resolveCondition(rule.condition),
            taint = rule.taint.flatMap { convertAssignActions(it) },
            info = rule.info,
        )
    }

    fun resolveAttributeSinks(
        serialized: List<SerializedPythonSink>,
        name: String,
    ): List<TaintSink> = resolveAttributeTargeted(serialized, name) { rule ->
        TaintSink(
            target = Target.Attribute(name),
            condition = resolveCondition(rule.condition),
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
            condition = resolveCondition(rule.condition),
            copy = rule.copy.flatMap { convertPassActions(it) },
        )
    }

    fun resolveAttributeCleaners(
        serialized: List<SerializedPythonCleaner>,
        name: String,
    ): List<TaintCleaner> = resolveAttributeTargeted(serialized, name) { rule ->
        TaintCleaner(
            target = Target.Attribute(name),
            condition = resolveCondition(rule.condition),
            cleans = rule.cleans.flatMap { convertCleanActions(it) },
            forCategory = rule.`for`,
            info = rule.info,
        )
    }

    // endregion

    /**
     * Shared scaffolding for source / entry-point resolution: match the rule against [method],
     * split `taint:` actions by `(decoratedWith, baseClass)` scope, drop scope groups that fail,
     * and hand each surviving group (with the matched method) to [build].
     */
    private inline fun <S : SerializedPythonSourceRule, T> resolveSourceRule(
        serialized: List<S>,
        build: (PIRCondition, List<TaintAssignAction>, PIRFunction, ItemInfo?) -> T,
    ): List<T> {
        requireMethod(method)

        return serialized.flatMap { rule ->
            val fn = rule.target as? PythonTarget.Function ?: return@flatMap emptyList()
            if (!fn.matches(method)) return@flatMap emptyList()

            val baseCondition = resolveCondition(rule.condition)
            rule.taint.groupBy { it.decoratedWith to it.baseClass }
                .mapNotNull { (scope, actions) ->
                    val (decoratedWith, baseClass) = scope
                    if (decoratedWith != null && !method.hasDecorator(decoratedWith)) return@mapNotNull null
                    if (baseClass != null && !method.hasBaseClass(baseClass)) return@mapNotNull null
                    build(baseCondition, actions.flatMap { convertAssignActions(it) }, method, rule.info)
                }
        }
    }

    /** Match a function-target rule (sinks / passthrough / cleaners) against [method]. */
    private inline fun <S : SerializedPythonRule, T> resolveFunctionTargeted(
        serialized: List<S>,
        build: (S, PythonTarget.Function, PIRFunction) -> T,
    ): List<T> {
        requireMethod(method)

        return serialized.mapNotNull { rule ->
            val fn = rule.target as? PythonTarget.Function ?: return@mapNotNull null
            if (!fn.matches(method)) return@mapNotNull null
            build(rule, fn, method)
        }
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
        val ctorName = if (ctorQn != qn) ctorQn.substringAfterLast('.') else method.name

        return when {
            hasRegexMetaChar(name) -> {
                val rx = Regex(name)
                rx.matches(qn) || (ctorQn != qn && rx.matches(ctorQn))
            }
            '.' in name -> qn == name || ctorQn == name
            else -> method.name == name || ctorName == name
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

    /**
     * Positional-argument index space of a call to this method, receiver excluded —
     * aligned with `PIRCall.args` (so `arg(*)` expands to exactly these). Drops the
     * implicit `self` / `cls` slot via [declaredParameters].
     */
    private fun PIRFunction.argumentIndices(): List<Int> = declaredParameters().indices.toList()

    private fun PIRFunction.hasDecorator(fqn: String): Boolean =
        decorators.any { it.qualifiedName == fqn }

    private fun PIRFunction.hasBaseClass(fqn: String): Boolean =
        enclosingClass?.let { fqn in it.mro } == true

    // endregion

    // region Position + condition + action conversion

    private fun convertAssignActions(a: SerializedPythonTaintAssignAction): List<TaintAssignAction> =
        expandPositions(a.pos).map { TaintAssignAction(mark = TaintMark(a.kind), pos = it) }

    private fun convertCleanActions(a: SerializedPythonTaintCleanAction): List<TaintCleanAction> =
        expandPositions(a.pos).map { TaintCleanAction(mark = TaintMark(a.taintKind), pos = it) }

    private fun convertPassActions(a: SerializedPythonTaintPassAction): List<TaintPassAction> {
        val mark = a.taintKind?.let(::TaintMark)
        val froms = expandPositions(a.from)
        val tos = expandPositions(a.to)
        return froms.flatMap { from -> tos.map { to -> TaintPassAction(mark, from, to) } }
    }

    /**
     * Resolve a serialized position to one or more runtime positions. `arg(*)`
     * ([PythonPositionBase.Argument] with a null index) has no single access path, so it is
     * expanded against the matched method's positional arguments into one concrete `arg(i)` per
     * argument; every other base resolves to exactly one position.
     */
    private fun expandPositions(p: PythonPosition): List<Position> {
        val base = p.base
        // TODO kw-params
        if (base is PythonPositionBase.Argument && base.idx == null) {
            return argIndices.mapNotNull { convertPosition(p.withBase(PythonPositionBase.Argument(it))) }
        }
        return listOfNotNull(convertPosition(p))
    }

    private fun PythonPosition.withBase(newBase: PythonPositionBase): PythonPosition = when (this) {
        is PythonPosition.BaseOnly -> PythonPosition.BaseOnly(newBase)
        is PythonPosition.WithModifiers -> PythonPosition.WithModifiers(newBase, modifiers)
    }

    private fun convertPosition(p: PythonPosition): Position? {
        val base = convertBase(p.base) ?: return null
        return when (p) {
            is PythonPosition.BaseOnly -> base
            is PythonPosition.WithModifiers -> p.modifiers.fold(base) { acc, mod ->
                PositionWithAccess(acc, convertAccessor(mod))
            }
        }
    }

    private fun convertBase(base: PythonPositionBase): Position? = when (base) {
        is PythonPositionBase.Argument -> {
            val idx = base.idx ?: return AllArguments

            Argument(idx).takeIf { isValidArgIndex(idx) }
        }
        is PythonPositionBase.KwArgument -> KwArgument(base.name)
        PythonPositionBase.This -> This
        PythonPositionBase.Result -> Result
        is PythonPositionBase.ClassRef -> ClassRef(base.fqn)
    }

    private fun isValidArgIndex(idx: Int): Boolean = idx in argIndices

    private fun convertAccessor(m: PythonPositionModifier): PositionAccessor = when (m) {
        PythonPositionModifier.ArrayElement -> PositionAccessor.ElementAccessor
        is PythonPositionModifier.Field -> PositionAccessor.FieldAccessor(m.name)
    }

    private fun resolveCondition(c: SerializedPythonCondition?): PIRCondition =
        convertCondition(c).simplify()

    private fun convertCondition(c: SerializedPythonCondition?): PIRCondition = when (c) {
        null -> mkTrue()
        is SerializedPythonCondition.Or -> CommonCondition.Or(c.anyOf.map { convertCondition(it) })
        is SerializedPythonCondition.And -> CommonCondition.And(c.allOf.map { convertCondition(it) })
        is SerializedPythonCondition.Not -> CommonCondition.Not(convertCondition(c.not))
        is SerializedPythonCondition.ContainsMark -> containsMarkCondition(c)
        // Arity is resolved statically here: the call site is unavailable, but feasibility against
        // the matched signature is enough. Attribute targets (no method) carry no arity → mkTrue.
        is SerializedPythonCondition.NumberOfArgs -> {
            requireMethod(method)

            if (method.acceptsPositionalArity(c.n)) mkTrue() else mkFalse()
        }
        // Constant-argument predicates are folded against the actual call value at rewrite time
        // (PIRConditionRewriter); here we only carry the position + expected value as an atom.
        is SerializedPythonCondition.ConstantCmp ->
            mkOr(expandPositions(c.pos).map { atom(ConstantCmp(it, c.value.toEngineValue(), c.cmp.toEngineCmp())) })
        is SerializedPythonCondition.ConstantMatches ->
            mkOr(expandPositions(c.pos).map { atom(ConstantMatches(it, Regex(c.pattern))) })
    }

    private fun atom(a: PythonRuleCondition): PIRCondition = CommonCondition.Atom(a)

    private fun SerializedPythonCondition.ConstantValue.toEngineValue(): ConstantValue = when (type) {
        SerializedPythonCondition.ConstantType.Str -> StrConstantValue(value)
        SerializedPythonCondition.ConstantType.Int -> IntConstantValue(value.toLong())
        SerializedPythonCondition.ConstantType.Bool -> BoolConstantValue(value.toBooleanStrict())
    }

    private fun SerializedPythonCondition.ConstantCmpType.toEngineCmp(): ConstantCmpType = when (this) {
        SerializedPythonCondition.ConstantCmpType.Eq -> ConstantCmpType.Eq
        SerializedPythonCondition.ConstantCmpType.Lt -> ConstantCmpType.Lt
        SerializedPythonCondition.ConstantCmpType.Gt -> ConstantCmpType.Gt
    }

    /**
     * Whether a call passing exactly [n] positional arguments is feasible for this function.
     *
     * `n` comes from a `NumberOfArgsConstraint`, which the pattern layer emits ONLY for fully
     * positional, fixed-arity call patterns (`sink($X, $Y)`); patterns with keyword args, `*args`,
     * or `...` fall through to a different constraint and never produce it. So this is purely a
     * positional-slot question: only positional-capable params bound the range — keyword-only and
     * `**kwargs` params can never receive a positional argument, so they are irrelevant. Defaults
     * lower the minimum; `*args` removes the upper bound. An unknown callee has no real signature,
     * so the captured call shape stands in: the concrete positional count bounds the range, and a
     * spread (`*args` at the call) removes the upper bound.
     */
    private fun PIRFunction.acceptsPositionalArity(n: Int): Boolean {
        if (this is PIRUnknownFunction) {
            val positional = positionalArgIndices.size
            val max = if (hasVarPositionalArg) Int.MAX_VALUE else positional
            return n in positional..max
        }
        val positional = declaredParameters().filter {
            it.kind == PIRParameterKind.POSITIONAL_ONLY || it.kind == PIRParameterKind.POSITIONAL_OR_KEYWORD
        }
        val min = positional.count { !it.hasDefault }
        val hasVarArgs = declaredParameters().any { it.kind == PIRParameterKind.VAR_POSITIONAL }
        val max = if (hasVarArgs) Int.MAX_VALUE else positional.size
        return n in min..max
    }

    /** `ContainsMark` over `arg(*)` means "the mark is on some argument" — an [CommonCondition.Or] of per-arg atoms. */
    private fun containsMarkCondition(c: SerializedPythonCondition.ContainsMark): PIRCondition =
        mkOr(expandPositions(c.pos).map { atom(ContainsMark(mark = TaintMark(c.tainted), pos = it)) })

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

    @OptIn(ExperimentalContracts::class)
    private fun requireMethod(method: PIRFunction?) {
        contract { returns() implies (method != null) }
        requireNotNull(method) { "function-targeted resolution requires a method" }
    }

    companion object {
        private const val DEFAULT_SINK_MESSAGE = "taint reaches sink"
        private val REGEX_META_CHARS = setOf('*', '+', '?', '[', ']', '(', ')', '|', '^', '$', '\\', '{', '}')
    }
}
