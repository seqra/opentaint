package org.opentaint.semgrep.pattern.conversion

import kotlinx.serialization.Serializable

sealed interface SemgrepPatternAction {
    val metavars: List<MetavarAtom>
    val result: ParamCondition?
    fun setResultCondition(condition: ParamCondition): SemgrepPatternAction

    @Serializable
    sealed interface SignatureName {
        @Serializable
        data class Concrete(val name: String) : SignatureName {
            override fun toString(): String = name
        }

        @Serializable
        data class MetaVar(val metaVar: String) : SignatureName {
            override fun toString(): String = metaVar
        }

        @Serializable
        data object AnyName : SignatureName {
            override fun toString(): String = "*"
        }
    }

    data class MethodCall(
        val methodName: SignatureName,
        override val result: ParamCondition?,
        val params: ParamConstraint,
        val obj: ParamCondition?,
        val enclosingClassName: TypeConstraint?,
    ) : SemgrepPatternAction {
        override val metavars: List<MetavarAtom>
            get() {
                val metavars = mutableSetOf<MetavarAtom>()
                params.conditions.forEach { it.collectMetavarTo(metavars) }
                obj?.collectMetavarTo(metavars)
                result?.collectMetavarTo(metavars)
                return metavars.toList()
            }

        override fun setResultCondition(condition: ParamCondition): SemgrepPatternAction {
            return MethodCall(methodName, condition, params, obj, enclosingClassName)
        }
    }

    data class ConstructorCall(
        val className: TypeConstraint,
        override val result: ParamCondition?,
        val params: ParamConstraint,
    ) : SemgrepPatternAction {
        override val metavars: List<MetavarAtom>
            get() {
                val metavars = mutableSetOf<MetavarAtom>()
                params.conditions.forEach { it.collectMetavarTo(metavars) }
                result?.collectMetavarTo(metavars)
                return metavars.toList()
            }

        override fun setResultCondition(condition: ParamCondition): SemgrepPatternAction {
            return ConstructorCall(className, condition, params)
        }
    }

    @Serializable
    sealed interface SignatureModifierValue {
        @Serializable
        data object NoValue : SignatureModifierValue
        @Serializable
        data object AnyValue : SignatureModifierValue
        @Serializable
        data class StringValue(val paramName: String, val value: String) : SignatureModifierValue
        @Serializable
        data class StringPattern(val paramName: String, val pattern: String) : SignatureModifierValue
        @Serializable
        data class MetaVar(val paramName: String, val metaVar: String) : SignatureModifierValue
    }

    @Serializable
    sealed interface ClassConstraint {
        @Serializable
        data class Signature(val modifier: SignatureModifier) : ClassConstraint
        @Serializable
        data class SuperType(val superType: TypeConstraint) : ClassConstraint
    }

    @Serializable
    data class SignatureModifier(
        val type: TypeConstraint,
        val value: SignatureModifierValue
    )

    data class MethodSignature(
        val methodName: SignatureName,
        val params: ParamConstraint.Partial,
        val returnType: TypeConstraint? = null,
        val modifiers: List<SignatureModifier>,
        val enclosingClassMetavar: String?,
        val enclosingClassConstraints: List<ClassConstraint>,
    ): SemgrepPatternAction {
        override val metavars: List<MetavarAtom>
            get() {
                val metavars = mutableSetOf<MetavarAtom>()
                params.conditions.forEach { it.collectMetavarTo(metavars) }
                return metavars.toList()
            }

        override val result: ParamCondition? = null

        override fun setResultCondition(condition: ParamCondition): SemgrepPatternAction {
            error("Unsupported operation?")
        }
    }

    data class MethodExit(val retVals: List<ParamCondition>) : SemgrepPatternAction {
        override val metavars: List<MetavarAtom>
            get() {
                val metavars = mutableSetOf<MetavarAtom>()
                retVals.forEach { it.collectMetavarTo(metavars) }
                return metavars.toList()
            }

        override val result: ParamCondition? = null

        override fun setResultCondition(condition: ParamCondition): SemgrepPatternAction {
            error("Unsupported operation?")
        }
    }
}
