package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.ArgPrefix
import org.opentaint.semgrep.pattern.CallArgs
import org.opentaint.semgrep.pattern.CallExpr
import org.opentaint.semgrep.pattern.ConcreteName
import org.opentaint.semgrep.pattern.EllipsisArgPrefix
import org.opentaint.semgrep.pattern.ExprStmt
import org.opentaint.semgrep.pattern.Identifier
import org.opentaint.semgrep.pattern.IntLiteral
import org.opentaint.semgrep.pattern.MapType
import org.opentaint.semgrep.pattern.Metavar
import org.opentaint.semgrep.pattern.MetavarName
import org.opentaint.semgrep.pattern.MetavarType
import org.opentaint.semgrep.pattern.Name
import org.opentaint.semgrep.pattern.NamedType
import org.opentaint.semgrep.pattern.NilLiteral
import org.opentaint.semgrep.pattern.NoArgs
import org.opentaint.semgrep.pattern.ParenExpr
import org.opentaint.semgrep.pattern.PointerType
import org.opentaint.semgrep.pattern.QualifiedType
import org.opentaint.semgrep.pattern.SelectorExpr
import org.opentaint.semgrep.pattern.SemgrepGoPattern
import org.opentaint.semgrep.pattern.SliceType
import org.opentaint.semgrep.pattern.StringEllipsis
import org.opentaint.semgrep.pattern.StringLiteral
import org.opentaint.semgrep.pattern.TopList
import org.opentaint.semgrep.pattern.TypeName
import org.opentaint.semgrep.pattern.TypedMetavar
import org.opentaint.semgrep.pattern.Ellipsis
import org.opentaint.semgrep.pattern.EllipsisStmt
import org.opentaint.semgrep.pattern.AssignStmt
import org.opentaint.semgrep.pattern.FuncDecl
import org.opentaint.semgrep.pattern.MethodDecl
import org.opentaint.semgrep.pattern.FuncType
import org.opentaint.semgrep.pattern.ParameterDecl
import org.opentaint.semgrep.pattern.NamedParam
import org.opentaint.semgrep.pattern.EllipsisParam
import org.opentaint.semgrep.pattern.EllipsisMetavarParam
import org.opentaint.semgrep.pattern.MetavarParam
import org.opentaint.semgrep.pattern.BlockStmt
import org.opentaint.semgrep.pattern.ReturnStmt
import org.opentaint.semgrep.pattern.DeferStmt
import org.opentaint.semgrep.pattern.GoStmt
import org.opentaint.semgrep.pattern.ShortVarDecl
import org.opentaint.semgrep.pattern.VarDecl
import org.opentaint.semgrep.pattern.CompositeLit
import org.opentaint.semgrep.pattern.CompositeElem
import org.opentaint.semgrep.pattern.KeyedElem
import org.opentaint.semgrep.pattern.EllipsisElem
import org.opentaint.semgrep.pattern.UnaryExpr
import org.opentaint.semgrep.pattern.conversion.SemgrepGoPatternAction.ConstructorCall
import org.opentaint.semgrep.pattern.conversion.SemgrepGoPatternAction.MethodCall
import org.opentaint.semgrep.pattern.conversion.SemgrepGoPatternAction.MethodExit
import org.opentaint.semgrep.pattern.conversion.SemgrepGoPatternAction.MethodSignature
import org.opentaint.semgrep.pattern.conversion.SemgrepGoPatternAction.SignatureName

class PatternToActionListConverter {
    val failedTransformations = mutableMapOf<String, Int>()

    private var nextArtificialId = 0
    private fun provideArtificialMetavar(): MetavarAtom =
        MetavarAtom.createArtificial("${nextArtificialId++}")

    private class TransformationFailed(override val message: String) : Exception(message)
    private fun transformationFailed(reason: String): Nothing = throw TransformationFailed(reason)

    fun createActionList(pattern: SemgrepGoPattern): SemgrepGoPatternActionList? = try {
        transformPatternToActionList(pattern, isRoot = true)
    } catch (ex: TransformationFailed) {
        val reason = ex.message
        failedTransformations[reason] = (failedTransformations[reason] ?: 0) + 1
        null
    }

    private fun transformPatternToActionList(
        pattern: SemgrepGoPattern,
        isRoot: Boolean = false,
    ): SemgrepGoPatternActionList = when (pattern) {
        is TopList -> transformSequence(pattern.items)
        is ExprStmt -> transformPatternToActionList(pattern.expr)
        is CallExpr -> transformMethodInvocation(pattern)
        is Ellipsis, is EllipsisStmt ->
            SemgrepGoPatternActionList(emptyList(), hasEllipsisInTheBeginning = true, hasEllipsisInTheEnd = true)
        is DeferStmt -> transformPatternToActionList(pattern.call)
        is GoStmt -> transformPatternToActionList(pattern.call)
        is AssignStmt -> {
            if (pattern.op != "=") transformationFailed("Assignment_op_${pattern.op}")
            if (pattern.lhs.size != 1 || pattern.rhs.size != 1) transformationFailed("multi-LHS assignment")
            transformAssignment(pattern.lhs.single(), declType = null, value = pattern.rhs.single())
        }
        is ShortVarDecl -> {
            if (pattern.lhs.size != 1 || pattern.rhs.size != 1) transformationFailed("multi-LHS assignment")
            transformAssignment(pattern.lhs.single(), declType = null, value = pattern.rhs.single())
        }
        is VarDecl -> {
            val spec = pattern.specs.singleOrNull() ?: transformationFailed("VarDecl_multiple_specs")
            if (spec.names.size != 1 || spec.values.size != 1) transformationFailed("multi-LHS assignment")
            transformAssignment(target = null, targetName = spec.names.single(), declType = spec.type, value = spec.values.single())
        }
        is CompositeLit -> transformObjectCreation(pattern)
        is UnaryExpr ->
            if (pattern.op == "&" && pattern.operand is CompositeLit) transformObjectCreation(pattern.operand as CompositeLit)
            else transformationFailed("UnaryExpr_${pattern.op}")
        is FuncDecl -> transformFuncDecl(pattern.name, pattern.signature, pattern.body, receiverType = null)
        is MethodDecl -> {
            val recvType = (pattern.receiver as? NamedParam)?.type?.let { transformType(it) }
            transformFuncDecl(pattern.name, pattern.signature, pattern.body, receiverType = recvType)
        }
        is BlockStmt -> transformSequence(pattern.stmts)
        is ReturnStmt -> {
            val retVals = pattern.values.map { v ->
                val (actions, cond) = transformPatternIntoParamConditionWithActions(v)
                check(actions.isEmpty()) { "return values with side effects are not supported in v1" }
                cond ?: ParamCondition.True
            }
            SemgrepGoPatternActionList(
                listOf(MethodExit(retVals)),
                hasEllipsisInTheBeginning = false,
                hasEllipsisInTheEnd = false,
            )
        }
        // Cases added in later tasks.
        else -> {
            val prefix = if (isRoot) "Root pattern is: " else ""
            transformationFailed("$prefix${pattern::class.simpleName}")
        }
    }

    private fun transformSequence(items: List<SemgrepGoPattern>): SemgrepGoPatternActionList {
        if (items.isEmpty()) {
            return SemgrepGoPatternActionList(emptyList(), hasEllipsisInTheBeginning = false, hasEllipsisInTheEnd = false)
        }
        return items
            .map { transformPatternToActionList(it) }
            .reduce { acc, next -> concatActionLists(acc, next) }
    }

    private fun concatActionLists(
        first: SemgrepGoPatternActionList,
        second: SemgrepGoPatternActionList,
    ): SemgrepGoPatternActionList {
        var endEllipsis = second.hasEllipsisInTheEnd
        if (endEllipsis && second.actions.isEmpty() && first.actions.lastOrNull() is MethodExit) {
            endEllipsis = false
        }
        // A leading "..." (empty list, both flags) contributes only the beginning flag.
        val beginEllipsis = first.hasEllipsisInTheBeginning
        return SemgrepGoPatternActionList(
            first.actions + second.actions,
            hasEllipsisInTheBeginning = beginEllipsis,
            hasEllipsisInTheEnd = endEllipsis,
        )
    }

    private fun signatureName(name: Name): SignatureName = when (name) {
        is ConcreteName -> SignatureName.Concrete(name.name)
        is MetavarName -> SignatureName.MetaVar(name.name)
    }

    private fun transformMethodInvocation(call: CallExpr): SemgrepGoPatternActionList {
        val actions = mutableListOf<SemgrepGoPatternAction>()
        val methodName: SignatureName
        var obj: ParamCondition? = null
        var enclosing: TypePattern? = null

        when (val fn = call.fn) {
            is Identifier -> methodName = signatureName(fn.name)
            is Metavar -> methodName = SignatureName.MetaVar(fn.name)
            is SelectorExpr -> {
                methodName = signatureName(fn.sel)
                // A package-qualified call `pkg.Func(...)` arrives here too: the parser models the
                // receiver `pkg` as Identifier(ConcreteName), which decomposeReceiver maps to
                // (obj = True, enclosingClassName = Named(pkg)).
                val (recvActions, recvObj, recvType) = decomposeReceiver(fn.obj)
                actions += recvActions
                obj = recvObj
                enclosing = recvType
            }
            else -> transformationFailed("MethodInvocation_fn: ${fn::class.simpleName}")
        }

        // TODO: CallExpr.hasEllipsis (Go variadic spread, e.g. f(xs...)) is not yet modeled.
        val (argActions, params) = generateParamConditions(call.args)
        actions += argActions
        actions += MethodCall(methodName, obj, enclosing, params, result = null)
        return SemgrepGoPatternActionList(actions, hasEllipsisInTheBeginning = false, hasEllipsisInTheEnd = false)
    }

    private fun decomposeReceiver(
        recv: SemgrepGoPattern,
    ): Triple<List<SemgrepGoPatternAction>, ParamCondition?, TypePattern?> = when (recv) {
        is Identifier -> when (val n = recv.name) {
            is ConcreteName -> Triple(emptyList(), ParamCondition.True, TypePattern.Named(n.name))
            is MetavarName -> Triple(emptyList(), ParamCondition.IsMetavar(MetavarAtom.create(n.name)), null)
        }
        is Metavar -> Triple(emptyList(), ParamCondition.IsMetavar(MetavarAtom.create(recv.name)), null)
        is TypedMetavar -> {
            val t = transformType(recv.type)
            Triple(
                emptyList(),
                ParamCondition.And(listOf(ParamCondition.IsMetavar(MetavarAtom.create(recv.name)), ParamCondition.TypeIs(t))),
                t,
            )
        }
        is ParenExpr -> decomposeReceiver(recv.inner)
        is CallExpr -> {
            val (actions, cond) = transformPatternIntoParamConditionWithActions(recv)
            Triple(actions, cond ?: ParamCondition.True, null)
        }
        else -> transformationFailed("MethodInvocation_obj: ${recv::class.simpleName}")
    }

    private fun flattenArgs(args: CallArgs): List<SemgrepGoPattern?> {
        val out = mutableListOf<SemgrepGoPattern?>()
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
    ): Pair<List<SemgrepGoPatternAction>, ParamConstraint> {
        val flat = flattenArgs(args)
        val allActions = mutableListOf<SemgrepGoPatternAction>()
        val patterns = mutableListOf<ParamPattern>()
        var idxConcrete = true
        for ((i, arg) in flat.withIndex()) {
            if (arg == null) { idxConcrete = false; continue }
            val (actions, cond) = transformPatternIntoParamConditionWithActions(arg)
            allActions += actions
            val position: ParamPosition =
                if (idxConcrete) ParamPosition.Concrete(i) else ParamPosition.Any(argClassifier(arg, i))
            val condition = cond ?: ParamCondition.True
            if (condition is ParamCondition.True && position is ParamPosition.Any) continue
            patterns += ParamPattern(position, condition)
        }
        if (idxConcrete) {
            return allActions to ParamConstraint.Concrete(patterns.map { it.condition })
        }
        if (patterns.count { it.position is ParamPosition.Any } > 1) transformationFailed("Multiple any params")
        return allActions to ParamConstraint.Partial(patterns)
    }

    private fun argClassifier(arg: SemgrepGoPattern, i: Int): String = when (arg) {
        is Metavar -> arg.name
        is TypedMetavar -> arg.name
        else -> "*->$i"
    }

    /** Returns (prefix actions, condition?). A simple value yields (emptyList, cond). A complex
     *  sub-expression yields its actions with the last result bound to a fresh artificial metavar. */
    private fun transformPatternIntoParamConditionWithActions(
        pattern: SemgrepGoPattern,
    ): Pair<List<SemgrepGoPatternAction>, ParamCondition?> {
        transformPatternIntoParamCondition(pattern)?.let { return emptyList<SemgrepGoPatternAction>() to it }
        val actionList = transformPatternToActionList(pattern)
        if (actionList.actions.isEmpty()) return emptyList<SemgrepGoPatternAction>() to null
        val result = actionList.actions.toMutableList()
        val last = result.removeLast()
        val metavar = provideArtificialMetavar()
        result += last.setResultCondition(ParamCondition.IsMetavar(metavar))
        return result to ParamCondition.IsMetavar(metavar)
    }

    private fun transformPatternIntoParamCondition(pattern: SemgrepGoPattern): ParamCondition? = when (pattern) {
        is IntLiteral -> ParamCondition.SpecificIntValue(pattern.text)
        is NilLiteral -> ParamCondition.SpecificNilValue
        // Go's `true`/`false` are predeclared identifiers, not literals, so the parser
        // emits Identifier here (never BoolConstant). Other bare identifiers are not
        // simple values and fall through to null (deferred, like Java).
        is Identifier -> when ((pattern.name as? ConcreteName)?.name) {
            "true" -> ParamCondition.SpecificBoolValue(true)
            "false" -> ParamCondition.SpecificBoolValue(false)
            else -> null
        }
        is StringLiteral -> when (val c = pattern.content) {
            is ConcreteName -> ParamCondition.SpecificStringValue(c.name)
            is MetavarName -> ParamCondition.StringValueMetaVar(MetavarAtom.create(c.name))
        }
        is StringEllipsis -> ParamCondition.AnyStringLiteral
        is Metavar -> ParamCondition.IsMetavar(MetavarAtom.create(pattern.name))
        is TypedMetavar -> ParamCondition.And(
            listOf(
                ParamCondition.IsMetavar(MetavarAtom.create(pattern.name)),
                ParamCondition.TypeIs(transformType(pattern.type)),
            ),
        )
        else -> null
    }

    private fun transformAssignment(
        target: SemgrepGoPattern?,
        declType: TypeName?,
        value: SemgrepGoPattern,
        targetName: Name? = null,
    ): SemgrepGoPatternActionList {
        val conditions = mutableListOf<ParamCondition>()
        declType?.let { conditions += ParamCondition.TypeIs(transformType(it)) }

        val name: String = when {
            targetName != null -> (targetName as? MetavarName)?.name
                ?: transformationFailed("Assignment_target_not_metavar")
            target is Metavar -> target.name
            target is TypedMetavar -> {
                conditions += ParamCondition.TypeIs(transformType(target.type)); target.name
            }
            target is Identifier && target.name is MetavarName -> (target.name as MetavarName).name
            else -> transformationFailed("Assignment_target_not_metavar")
        }
        conditions += ParamCondition.IsMetavar(MetavarAtom.create(name))

        val actionList = transformPatternToActionList(value)
        if (actionList.actions.isEmpty()) transformationFailed("Assignment_nothing_to_assign")
        val last = actionList.actions.last()
        val newLast = last.setResultCondition(mkAnd(conditions))
        return SemgrepGoPatternActionList(
            actionList.actions.dropLast(1) + newLast,
            hasEllipsisInTheBeginning = false,
            hasEllipsisInTheEnd = false,
        )
    }

    private fun transformType(type: TypeName): TypePattern = when (type) {
        is NamedType -> when (val n = type.name) {
            is ConcreteName -> TypePattern.Named(n.name)
            is MetavarName -> TypePattern.MetaVar(n.name)
        }
        is QualifiedType -> {
            val pkg = (type.pkg as? ConcreteName)?.name ?: transformationFailed("QualifiedType_pkg_not_concrete")
            val name = (type.name as? ConcreteName)?.name ?: transformationFailed("QualifiedType_name_not_concrete")
            TypePattern.Qualified(pkg, name)
        }
        is MetavarType -> TypePattern.MetaVar(type.name)
        is PointerType -> TypePattern.Pointer(transformType(type.elem))
        is SliceType -> TypePattern.Slice(transformType(type.elem))
        is MapType -> TypePattern.Map(transformType(type.key), transformType(type.value))
        else -> transformationFailed("Type_unsupported: ${type::class.simpleName}")
    }

    private fun transformObjectCreation(lit: CompositeLit): SemgrepGoPatternActionList {
        val className = lit.type?.let { transformType(it) } ?: transformationFailed("CompositeLit_no_type")
        val allActions = mutableListOf<SemgrepGoPatternAction>()
        val patterns = mutableListOf<ParamPattern>()
        var positional = true
        var idx = 0
        for (elem in lit.elements) {
            when (elem) {
                is EllipsisElem -> positional = false
                is KeyedElem -> {
                    // `...` inside a composite literal is parsed as KeyedElem(null, Ellipsis) by the grammar.
                    // Treat it the same as EllipsisElem: it marks the struct literal as open/partial.
                    if (elem.key == null && elem.value is Ellipsis) { positional = false; continue }
                    val (actions, cond) = transformPatternIntoParamConditionWithActions(elem.value)
                    allActions += actions
                    val condition = cond ?: ParamCondition.True
                    val key = elem.key
                    val position: ParamPosition = when {
                        key != null -> ParamPosition.Named(
                            fieldName(key) ?: transformationFailed("CompositeLit_key_not_field"),
                        )
                        positional -> ParamPosition.Concrete(idx)
                        else -> ParamPosition.Any("*->$idx")
                    }
                    if (!(condition is ParamCondition.True && position is ParamPosition.Any)) {
                        patterns += ParamPattern(position, condition)
                    }
                    idx++
                }
            }
        }
        val allConcrete = positional && patterns.all { it.position is ParamPosition.Concrete }
        val params: ParamConstraint = if (allConcrete) {
            ParamConstraint.Concrete(patterns.map { it.condition })
        } else {
            if (patterns.count { it.position is ParamPosition.Any } > 1) transformationFailed("Multiple any params")
            ParamConstraint.Partial(patterns)
        }
        return SemgrepGoPatternActionList(
            allActions + ConstructorCall(className, params, result = null),
            hasEllipsisInTheBeginning = false,
            hasEllipsisInTheEnd = false,
        )
    }

    private fun fieldName(key: SemgrepGoPattern): String? = when (key) {
        is Identifier -> (key.name as? ConcreteName)?.name
        else -> null
    }

    private fun transformFuncDecl(
        name: Name,
        signature: FuncType,
        body: BlockStmt?,
        receiverType: TypePattern?,
    ): SemgrepGoPatternActionList {
        val methodName = signatureName(name)
        val paramPatterns = mutableListOf<ParamPattern>()
        var positional = true
        var idx = 0
        for (p in signature.params) {
            when (p) {
                is EllipsisParam, is EllipsisMetavarParam -> positional = false
                is MetavarParam -> {
                    val position = if (positional) ParamPosition.Concrete(idx) else ParamPosition.Any(p.name)
                    paramPatterns += ParamPattern(position, ParamCondition.IsMetavar(MetavarAtom.create(p.name)))
                    idx++
                }
                is NamedParam -> {
                    for (nm in p.names) {
                        val mv = (nm as? MetavarName)?.name
                            ?: transformationFailed("MethodDecl_param_name_not_metavar")
                        val position = if (positional) ParamPosition.Concrete(idx) else ParamPosition.Any(mv)
                        paramPatterns += ParamPattern(position, ParamCondition.IsMetavar(MetavarAtom.create(mv)))
                        paramPatterns += ParamPattern(position, ParamCondition.TypeIs(transformType(p.type)))
                        idx++
                    }
                }
            }
        }
        val returnTypes = signature.results.mapNotNull { (it as? NamedParam)?.type?.let { t -> transformType(t) } }
        val sig = MethodSignature(methodName, ParamConstraint.Partial(paramPatterns), returnTypes, receiverType)
        val bodyList = body?.let { transformPatternToActionList(it) }
        return SemgrepGoPatternActionList(
            listOf(sig) + (bodyList?.actions ?: emptyList()),
            hasEllipsisInTheBeginning = false,
            hasEllipsisInTheEnd = bodyList?.hasEllipsisInTheEnd ?: false,
        )
    }
}
