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
import org.opentaint.semgrep.pattern.QualifiedIdent
import org.opentaint.semgrep.pattern.QualifiedType
import org.opentaint.semgrep.pattern.SelectorExpr
import org.opentaint.semgrep.pattern.SemgrepGoPattern
import org.opentaint.semgrep.pattern.SliceType
import org.opentaint.semgrep.pattern.StringEllipsis
import org.opentaint.semgrep.pattern.StringLiteral
import org.opentaint.semgrep.pattern.TopList
import org.opentaint.semgrep.pattern.TypeName
import org.opentaint.semgrep.pattern.TypedMetavar
import org.opentaint.semgrep.pattern.conversion.SemgrepGoPatternAction.MethodCall
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
        // Cases added in later tasks.
        else -> {
            val prefix = if (isRoot) "Root pattern is: " else ""
            transformationFailed("$prefix${pattern::class.simpleName}")
        }
    }

    /** Task 2 version: concatenate items, no ellipsis flags yet (refined in Task 4). */
    private fun transformSequence(items: List<SemgrepGoPattern>): SemgrepGoPatternActionList {
        val actions = items.flatMap { transformPatternToActionList(it).actions }
        return SemgrepGoPatternActionList(actions, hasEllipsisInTheBeginning = false, hasEllipsisInTheEnd = false)
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
            is QualifiedIdent -> {
                methodName = signatureName(fn.sel)
                enclosing = qualifierType(fn.pkg)
                obj = ParamCondition.True
            }
            is SelectorExpr -> {
                methodName = signatureName(fn.sel)
                val (recvActions, recvObj, recvType) = decomposeReceiver(fn.obj)
                actions += recvActions
                obj = recvObj
                enclosing = recvType
            }
            else -> transformationFailed("MethodInvocation_fn: ${fn::class.simpleName}")
        }

        val (argActions, params) = generateParamConditions(call.args)
        actions += argActions
        actions += MethodCall(methodName, obj, enclosing, params, result = null)
        return SemgrepGoPatternActionList(actions, hasEllipsisInTheBeginning = false, hasEllipsisInTheEnd = false)
    }

    private fun qualifierType(name: Name): TypePattern = when (name) {
        is ConcreteName -> TypePattern.Named(name.name)
        is MetavarName -> TypePattern.MetaVar(name.name)
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
}
