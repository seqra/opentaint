package org.opentaint.semgrep.pattern.conversion

sealed interface SemgrepGoPatternAction {
    val result: ParamCondition?
    fun setResultCondition(condition: ParamCondition): SemgrepGoPatternAction

    sealed interface SignatureName {
        data class Concrete(val name: String) : SignatureName
        data class MetaVar(val metaVar: String) : SignatureName
        data object AnyName : SignatureName
    }

    data class MethodCall(
        val methodName: SignatureName,
        val obj: ParamCondition?,
        val enclosingClassName: TypePattern?,
        val params: ParamConstraint,
        override val result: ParamCondition?,
    ) : SemgrepGoPatternAction {
        override fun setResultCondition(condition: ParamCondition): SemgrepGoPatternAction {
            check(result == null) { "Cannot overwrite existing result condition" }
            return copy(result = condition)
        }
    }

    data class ConstructorCall(
        val className: TypePattern,
        val params: ParamConstraint,
        override val result: ParamCondition?,
    ) : SemgrepGoPatternAction {
        override fun setResultCondition(condition: ParamCondition): SemgrepGoPatternAction {
            check(result == null) { "Cannot overwrite existing result condition" }
            return copy(result = condition)
        }
    }

    data class MethodSignature(
        val methodName: SignatureName,
        val params: ParamConstraint.Partial,
        val returnTypes: List<TypePattern>,
        val receiverType: TypePattern?,
    ) : SemgrepGoPatternAction {
        override val result: ParamCondition? get() = null
        override fun setResultCondition(condition: ParamCondition): SemgrepGoPatternAction =
            error("MethodSignature has no result")
    }

    data class MethodExit(val retVals: List<ParamCondition>) : SemgrepGoPatternAction {
        override val result: ParamCondition? get() = null
        override fun setResultCondition(condition: ParamCondition): SemgrepGoPatternAction =
            error("MethodExit has no result")
    }
}
