package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.ArgPrefix
import org.opentaint.semgrep.pattern.Assign
import org.opentaint.semgrep.pattern.Attribute
import org.opentaint.semgrep.pattern.Block
import org.opentaint.semgrep.pattern.BoolLiteral
import org.opentaint.semgrep.pattern.Call
import org.opentaint.semgrep.pattern.CallArgs
import org.opentaint.semgrep.pattern.ClassDef
import org.opentaint.semgrep.pattern.ConcreteName
import org.opentaint.semgrep.pattern.DoubleStarArgument
import org.opentaint.semgrep.pattern.DoubleStarParam
import org.opentaint.semgrep.pattern.Ellipsis
import org.opentaint.semgrep.pattern.EllipsisArgPrefix
import org.opentaint.semgrep.pattern.EllipsisMetavar
import org.opentaint.semgrep.pattern.EllipsisParam
import org.opentaint.semgrep.pattern.EllipsisStmt
import org.opentaint.semgrep.pattern.ExprStmt
import org.opentaint.semgrep.pattern.FunctionDef
import org.opentaint.semgrep.pattern.Identifier
import org.opentaint.semgrep.pattern.KeywordArgument
import org.opentaint.semgrep.pattern.Metavar
import org.opentaint.semgrep.pattern.MetavarName
import org.opentaint.semgrep.pattern.Name
import org.opentaint.semgrep.pattern.NamedParam
import org.opentaint.semgrep.pattern.NoArgs
import org.opentaint.semgrep.pattern.NoneLiteral
import org.opentaint.semgrep.pattern.NumberLiteral
import org.opentaint.semgrep.pattern.ReturnStmt
import org.opentaint.semgrep.pattern.SemgrepPythonPattern
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.StarArgument
import org.opentaint.semgrep.pattern.StarParam
import org.opentaint.semgrep.pattern.StringEllipsis
import org.opentaint.semgrep.pattern.StringLiteral
import org.opentaint.semgrep.pattern.TopList
import org.opentaint.semgrep.pattern.TupleExpr
import org.opentaint.semgrep.pattern.WithStmt
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.ClassConstraint
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.MethodCall
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.MethodExit
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.MethodSignature
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureModifier
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureModifierValue
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureName

class PythonPatternToActionListConverter : ActionListBuilder<SemgrepPythonPattern> {
    val failedTransformations = mutableMapOf<String, Int>()

    private var nextArtificialId = 0
    private fun provideArtificialMetavar(): MetavarAtom =
        MetavarAtom.createArtificial("${nextArtificialId++}")

    private class TransformationFailed(override val message: String) : Exception(message)
    private fun transformationFailed(reason: String): Nothing = throw TransformationFailed(reason)

    override fun createActionList(
        pattern: SemgrepPythonPattern,
        semgrepTrace: SemgrepRuleLoadStepTrace,
    ): SemgrepPatternActionList? = try {
        transformPatternToActionList(pattern, isRoot = true)
    } catch (ex: TransformationFailed) {
        val reason = ex.message
        failedTransformations[reason] = (failedTransformations[reason] ?: 0) + 1
        null
    }

    private fun transformPatternToActionList(
        pattern: SemgrepPythonPattern,
        isRoot: Boolean = false,
    ): SemgrepPatternActionList = when (pattern) {
        is TopList -> transformSequence(pattern.items)
        is Block -> transformSequence(pattern.stmts)
        is ExprStmt -> transformPatternToActionList(pattern.expr)
        is Ellipsis, is EllipsisStmt ->
            SemgrepPatternActionList(emptyList(), hasEllipsisInTheBeginning = true, hasEllipsisInTheEnd = true)
        is Call -> transformMethodInvocation(pattern)
        is Attribute -> transformAttributeRead(pattern)
        is Assign -> transformAssignment(pattern)
        is ReturnStmt -> transformReturn(pattern)
        is FunctionDef -> transformFunctionDef(pattern)
        is ClassDef -> transformClassDef(pattern)
        is WithStmt -> transformWith(pattern)
        else -> {
            val prefix = if (isRoot) "Root pattern is: " else ""
            transformationFailed("$prefix${pattern::class.simpleName}")
        }
    }

    private fun transformSequence(items: List<SemgrepPythonPattern>): SemgrepPatternActionList {
        if (items.isEmpty()) {
            return SemgrepPatternActionList(emptyList(), hasEllipsisInTheBeginning = false, hasEllipsisInTheEnd = false)
        }
        return items
            .map { transformPatternToActionList(it) }
            .reduce { acc, next -> concatActionLists(acc, next) }
    }

    private fun concatActionLists(
        first: SemgrepPatternActionList,
        second: SemgrepPatternActionList,
    ): SemgrepPatternActionList {
        var endEllipsis = second.hasEllipsisInTheEnd
        if (endEllipsis && second.actions.isEmpty() && first.actions.lastOrNull() is MethodExit) {
            endEllipsis = false
        }
        // A leading "..." (empty list, both flags) contributes only the beginning flag.
        val beginEllipsis = first.hasEllipsisInTheBeginning
        return SemgrepPatternActionList(
            first.actions + second.actions,
            hasEllipsisInTheBeginning = beginEllipsis,
            hasEllipsisInTheEnd = endEllipsis,
        )
    }

    private fun signatureName(name: Name): SignatureName = when (name) {
        is ConcreteName -> SignatureName.Concrete(name.name)
        is MetavarName -> SignatureName.MetaVar(name.name)
    }

    private fun transformMethodInvocation(call: Call): SemgrepPatternActionList {
        val methodName: SignatureName
        var obj: ParamCondition? = null
        var enclosing: TypeConstraint? = null
        var receiverPrefixActions: List<SemgrepPatternAction> = emptyList()

        when (val fn = call.fn) {
            is Identifier -> methodName = signatureName(fn.name)
            is Metavar -> methodName = SignatureName.MetaVar(fn.name)
            is Attribute -> {
                methodName = signatureName(fn.name)
                val binding = resolveReceiver(fn.obj)
                receiverPrefixActions = binding.prefixActions
                obj = binding.obj
                enclosing = binding.enclosing
            }
            else -> transformationFailed("MethodInvocation_fn: ${fn::class.simpleName}")
        }

        val (argActions, params) = generateParamConditions(call.args)
        return SemgrepPatternActionList(
            receiverPrefixActions + argActions +
                MethodCall(methodName = methodName, result = null, params = params, obj = obj, enclosingClassName = enclosing),
            hasEllipsisInTheBeginning = false,
            hasEllipsisInTheEnd = false,
        )
    }

    /**
     * Bare attribute read `recv.attr` modeled as a synthetic, zero-arg method call whose name
     * carries [PythonLanguageStrategy.ATTR_READ_AUX_FN_PREFIX]; rule generation unpacks it into
     * an attribute target. The result is left unbound here — an enclosing assignment binds it.
     */
    private fun transformAttributeRead(attr: Attribute): SemgrepPatternActionList {
        val attrName = (attr.name as? ConcreteName)?.name
            ?: transformationFailed("AttributeRead_name_metavar")
        val methodName = SignatureName.Concrete(PythonLanguageStrategy.attrReadAuxFnName(attrName))

        val binding = resolveReceiver(attr.obj)
        return SemgrepPatternActionList(
            binding.prefixActions +
                MethodCall(
                    methodName = methodName,
                    result = null,
                    params = ParamConstraint.Concrete(emptyList()),
                    obj = binding.obj,
                    enclosingClassName = binding.enclosing,
                ),
            hasEllipsisInTheBeginning = false,
            hasEllipsisInTheEnd = false,
        )
    }

    private data class ReceiverBinding(
        val prefixActions: List<SemgrepPatternAction>,
        val obj: ParamCondition,
        val enclosing: TypeConstraint?,
    )

    /**
     * Lowers a receiver of an attribute read / method call into prefix actions plus the condition
     * to match it against. A bare metavar or an all-concrete dotted path bind directly; a
     * metavar-based chain (`$A.attr1.attr2`) is recursively lowered into artificial-metavar-bound
     * prefix actions so `$A.attr1.attr2.call1()` becomes `$T1 = $A.attr1; $T2 = $T1.attr2; ... $T2.call1()`.
     */
    private fun resolveReceiver(recv: SemgrepPythonPattern): ReceiverBinding {
        if (recv is Metavar) {
            return ReceiverBinding(emptyList(), IsMetavar(MetavarAtom.create(recv.name)), null)
        }
        // Keep the concrete-path check first so `a.b.c.func(...)` stays a qualified enclosing name
        // rather than being split into chained temporaries.
        concreteDottedNameOrNull(recv)?.let {
            return ReceiverBinding(emptyList(), ParamCondition.True, pythonNamed(it))
        }
        val (actions, cond) = transformPatternIntoParamConditionWithActions(recv)
        val obj = cond ?: transformationFailed("Receiver_unsupported")
        return ReceiverBinding(actions, obj, null)
    }

    /** All-concrete dotted path (`os`, `flask.views`) or null. */
    private fun concreteDottedNameOrNull(pattern: SemgrepPythonPattern): String? = when (pattern) {
        is Identifier -> (pattern.name as? ConcreteName)?.name
        is Attribute -> {
            val prefix = concreteDottedNameOrNull(pattern.obj)
            val name = (pattern.name as? ConcreteName)?.name
            if (prefix != null && name != null) "$prefix.$name" else null
        }
        else -> null
    }

    private fun flattenArgs(args: CallArgs): List<SemgrepPythonPattern?> {
        val out = mutableListOf<SemgrepPythonPattern?>()
        var cur: CallArgs = args
        while (true) {
            when (val c = cur) {
                is NoArgs -> return out
                is EllipsisArgPrefix -> { out.add(null); cur = c.rest }
                is ArgPrefix -> { out.add(c.arg); cur = c.rest }
            }
        }
    }

    private fun generateParamConditions(
        args: CallArgs,
    ): Pair<List<SemgrepPatternAction>, ParamConstraint> {
        val flat = flattenArgs(args)
        val allActions = mutableListOf<SemgrepPatternAction>()
        val patterns = mutableListOf<ParamPattern>()
        var idxConcrete = true
        var hasNamed = false
        var idx = 0
        for (arg in flat) {
            when (arg) {
                null, is EllipsisMetavar -> idxConcrete = false
                is StarArgument -> transformationFailed("Call_star_argument")
                is DoubleStarArgument -> transformationFailed("Call_doublestar_argument")
                is KeywordArgument -> {
                    hasNamed = true
                    val key = (arg.name as? ConcreteName)?.name
                        ?: transformationFailed("KeywordArgument_name_metavar")
                    val (actions, cond) = transformPatternIntoParamConditionWithActions(arg.value)
                    allActions += actions
                    patterns += ParamPattern(ParamPosition.Named(key), cond ?: ParamCondition.True)
                }

                else -> {
                    val (actions, cond) = transformPatternIntoParamConditionWithActions(arg)
                    allActions += actions
                    val position: ParamPosition =
                        if (idxConcrete) ParamPosition.Concrete(idx) else ParamPosition.Any(argClassifier(arg, idx))
                    val condition = cond ?: ParamCondition.True

                    idx++
                    if (condition is ParamCondition.True && position is ParamPosition.Any) continue
                    patterns += ParamPattern(position, condition)
                }
            }
        }
        if (idxConcrete && !hasNamed) {
            return allActions to ParamConstraint.Concrete(patterns.map { it.condition })
        }
        if (patterns.count { it.position is ParamPosition.Any } > 1) transformationFailed("Multiple any params")
        return allActions to ParamConstraint.Partial(patterns)
    }

    private fun argClassifier(arg: SemgrepPythonPattern, i: Int): String = when (arg) {
        is Metavar -> arg.name
        else -> "*->$i"
    }

    /** Returns (prefix actions, condition?). A simple value yields (emptyList, cond). A complex
     *  sub-expression yields its actions with the last result bound to a fresh artificial metavar. */
    private fun transformPatternIntoParamConditionWithActions(
        pattern: SemgrepPythonPattern,
    ): Pair<List<SemgrepPatternAction>, ParamCondition?> {
        transformPatternIntoParamCondition(pattern)?.let { return emptyList<SemgrepPatternAction>() to it }
        val actionList = transformPatternToActionList(pattern)
        if (actionList.actions.isEmpty()) return emptyList<SemgrepPatternAction>() to null
        val (result, metavar) = actionList.actions.ensureLastActionMetaVar()
        return result to IsMetavar(metavar)
    }

    private fun List<SemgrepPatternAction>.ensureLastActionMetaVar(): Pair<List<SemgrepPatternAction>, MetavarAtom> {
        val lastAction = last()
        val lastResult = lastAction.result
        if (lastResult != null) {
            val metaVars = hashSetOf<MetavarAtom>()
            lastResult.collectMetavarTo(metaVars)
            val metaVar = metaVars.singleOrNull()
                ?: error("Last action result has no or multiple meta-var")
            return this to metaVar
        }

        val result = toMutableList()
        val metavar = provideArtificialMetavar()
        val newLastAction = lastAction.setResultCondition(IsMetavar(metavar))
        result[result.lastIndex] = newLastAction
        return result to metavar
    }

    private fun transformPatternIntoParamCondition(pattern: SemgrepPythonPattern): ParamCondition? = when (pattern) {
        is NumberLiteral -> pattern.text.toIntOrNull()?.let { SpecificIntValue(it) }
            ?: transformationFailed("NumberLiteral_not_int: ${pattern.text}")
        is BoolLiteral -> SpecificBoolValue(pattern.value)
        is NoneLiteral -> SpecificNullValue
        // `True`/`False` lex via the grammar's `name` rule, so the parser emits Identifier
        // here (never BoolLiteral). Other bare identifiers are not simple values and fall
        // through to null.
        is Identifier -> when ((pattern.name as? ConcreteName)?.name) {
            "True" -> SpecificBoolValue(true)
            "False" -> SpecificBoolValue(false)
            else -> null
        }
        is StringLiteral -> when (val c = pattern.content) {
            is ConcreteName -> SpecificStringValue(c.name)
            is MetavarName -> ParamCondition.StringValueMetaVar(MetavarAtom.create(c.name))
        }
        is StringEllipsis -> ParamCondition.AnyStringLiteral
        is Metavar -> IsMetavar(MetavarAtom.create(pattern.name))
        else -> null
    }

    private fun transformAssignment(assign: Assign): SemgrepPatternActionList {
        if (assign.op != "=") transformationFailed("Assignment_op_${assign.op}")
        val target = assign.targets.singleOrNull() ?: transformationFailed("Assignment_chained")
        val value = assign.value ?: transformationFailed("Assignment_no_value")

        if (target is TupleExpr) transformationFailed("Assignment_tuple_target")

        // Only metavar targets bind a result; attribute/subscript stores are not modeled.
        val name = when {
            target is Metavar -> target.name
            target is Identifier && target.name is MetavarName -> (target.name as MetavarName).name
            else -> transformationFailed("Assignment_target_not_metavar")
        }

        val conditions = mutableListOf<ParamCondition>()
        assign.annotation?.let { conditions += ParamCondition.TypeIs(transformAnnotationType(it)) }
        conditions += IsMetavar(MetavarAtom.create(name))
        return transformAssignmentValue(conditions, value)
    }

    private fun transformAssignmentValue(
        conditions: List<ParamCondition>,
        value: SemgrepPythonPattern,
    ): SemgrepPatternActionList {
        val actionList = transformPatternToActionList(value)
        if (actionList.actions.isEmpty()) transformationFailed("Assignment_nothing_to_assign")
        val last = actionList.actions.last()
        val newLast = last.setResultCondition(mkAnd(conditions.toSet()))
        return SemgrepPatternActionList(
            actionList.actions.dropLast(1) + newLast,
            hasEllipsisInTheBeginning = false,
            hasEllipsisInTheEnd = false,
        )
    }

    private fun transformAnnotationType(annotation: SemgrepPythonPattern): TypeConstraint = when {
        annotation is Metavar -> TypeConstraint.MetaVar(annotation.name)
        annotation is Identifier && annotation.name is MetavarName ->
            TypeConstraint.MetaVar(annotation.name.name)
        else -> concreteDottedNameOrNull(annotation)?.let { pythonNamed(it) }
            ?: transformationFailed("Annotation_unsupported: ${annotation::class.simpleName}")
    }

    private fun transformReturn(ret: ReturnStmt): SemgrepPatternActionList {
        val (actions, cond) = ret.value?.let { transformPatternIntoParamConditionWithActions(it) }
            ?: (emptyList<SemgrepPatternAction>() to null)
        return SemgrepPatternActionList(
            actions + MethodExit(listOf(cond ?: ParamCondition.True)),
            hasEllipsisInTheBeginning = false,
            hasEllipsisInTheEnd = false,
        )
    }

    private fun transformFunctionDef(fn: FunctionDef): SemgrepPatternActionList {
        val paramPatterns = mutableListOf<ParamPattern>()
        var positional = true
        var idx = 0
        for (p in fn.params) {
            when (p) {
                is EllipsisParam -> positional = false
                is StarParam, is DoubleStarParam -> transformationFailed("FunctionDef_star_param")
                is NamedParam -> {
                    val mv = (p.name as? MetavarName)?.name
                        ?: transformationFailed("FunctionDef_param_name_not_metavar")
                    val position = if (positional) ParamPosition.Concrete(idx) else ParamPosition.Any(mv)
                    paramPatterns += ParamPattern(position, IsMetavar(MetavarAtom.create(mv)))
                    p.annotation?.let {
                        paramPatterns += ParamPattern(position, ParamCondition.TypeIs(transformAnnotationType(it)))
                    }
                    idx++
                }
            }
        }
        val sig = MethodSignature(
            methodName = signatureName(fn.name),
            params = ParamConstraint.Partial(paramPatterns),
            returnType = fn.returns?.let { transformAnnotationType(it) },
            modifiers = fn.decorators.map { transformDecorator(it) },
            enclosingClassMetavar = null,
            enclosingClassConstraints = emptyList(),
        )
        val bodyList = transformPatternToActionList(fn.body)
        return SemgrepPatternActionList(
            listOf(sig) + bodyList.actions,
            hasEllipsisInTheBeginning = false,
            hasEllipsisInTheEnd = bodyList.hasEllipsisInTheEnd,
        )
    }

    private fun transformDecorator(decorator: SemgrepPythonPattern): SignatureModifier = when (decorator) {
        is Identifier, is Attribute, is Metavar ->
            SignatureModifier(transformAnnotationType(decorator), SignatureModifierValue.NoValue)
        is Call -> SignatureModifier(
            transformAnnotationType(decorator.fn),
            transformDecoratorValue(flattenArgs(decorator.args)),
        )
        else -> transformationFailed("Decorator_unsupported: ${decorator::class.simpleName}")
    }

    private fun transformDecoratorValue(args: List<SemgrepPythonPattern?>): SignatureModifierValue {
        if (args.isEmpty()) return SignatureModifierValue.NoValue

        val nonEllipsisArgs = args.filterNotNull().filterNot { it is EllipsisMetavar }
        if (nonEllipsisArgs.isEmpty()) return SignatureModifierValue.AnyValue

        val arg = nonEllipsisArgs.singleOrNull() ?: transformationFailed("Decorator_multiple_args")
        if (arg !is KeywordArgument) {
            return decoratorParamValue(arg, paramName = "value")
        }

        val paramName = (arg.name as? ConcreteName)?.name
            ?: transformationFailed("Decorator_argument_parameter_is_not_concrete")
        return decoratorParamValue(arg.value, paramName)
    }

    private fun decoratorParamValue(
        pattern: SemgrepPythonPattern,
        paramName: String,
    ): SignatureModifierValue = when (pattern) {
        is StringLiteral -> when (val content = pattern.content) {
            is ConcreteName -> SignatureModifierValue.StringValue(paramName, content.name)
            is MetavarName -> transformationFailed("Decorator_argument_is_string_with_meta_var")
        }
        is StringEllipsis -> SignatureModifierValue.StringPattern(paramName, pattern = ".*")
        is Metavar -> SignatureModifierValue.MetaVar(paramName, pattern.name)
        else -> transformationFailed("Decorator_argument_is_not_string_or_metavar")
    }

    private fun transformClassDef(cls: ClassDef): SemgrepPatternActionList {
        val nameMetavar = (cls.name as? MetavarName)?.name
            ?: transformationFailed("ClassDef_name_is_not_metavar")

        val classConstraints = mutableListOf<ClassConstraint>()
        for (base in flattenArgs(cls.bases)) {
            if (base == null || base is EllipsisMetavar) continue
            if (base is KeywordArgument) transformationFailed("ClassDef_keyword_base")
            classConstraints += ClassConstraint.SuperType(transformAnnotationType(base))
        }
        cls.decorators.mapTo(classConstraints) { ClassConstraint.Signature(transformDecorator(it)) }

        val bodyActionList = transformPatternToActionList(cls.body)
        if (bodyActionList.actions.isEmpty()) {
            val methodSignature = MethodSignature(
                methodName = SignatureName.AnyName,
                params = ParamConstraint.Partial(emptyList()),
                modifiers = emptyList(),
                enclosingClassMetavar = nameMetavar,
                enclosingClassConstraints = classConstraints,
            )
            return SemgrepPatternActionList(
                listOf(methodSignature),
                hasEllipsisInTheBeginning = false,
                hasEllipsisInTheEnd = true,
            )
        }

        val firstAction = bodyActionList.actions.first()
        if (firstAction !is MethodSignature) {
            transformationFailed("ClassDef_body_without_method_signature")
        }
        val signatureWithClass = firstAction.copy(
            enclosingClassMetavar = nameMetavar,
            enclosingClassConstraints = classConstraints,
        )
        return bodyActionList.copy(
            actions = listOf(signatureWithClass) + bodyActionList.actions.drop(1),
            hasEllipsisInTheBeginning = false,
        )
    }

    private fun transformWith(stmt: WithStmt): SemgrepPatternActionList {
        val itemLists = stmt.items.map { item ->
            val contextList = transformPatternToActionList(item.context)
            val asTarget = item.asTarget ?: return@map contextList
            val name = when {
                asTarget is Metavar -> asTarget.name
                asTarget is Identifier && asTarget.name is MetavarName -> (asTarget.name as MetavarName).name
                else -> transformationFailed("WithItem_target_not_metavar")
            }
            if (contextList.actions.isEmpty()) transformationFailed("WithItem_nothing_to_bind")
            val newLast = contextList.actions.last().setResultCondition(IsMetavar(MetavarAtom.create(name)))
            contextList.copy(actions = contextList.actions.dropLast(1) + newLast)
        }
        return (itemLists + transformPatternToActionList(stmt.body)).reduce { acc, next -> concatActionLists(acc, next) }
    }
}
