package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.mkAnd
import org.opentaint.dataflow.configuration.mkFalse
import org.opentaint.dataflow.configuration.mkOr
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.configuration.simplify
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.type.GoIRArrayType
import org.opentaint.ir.go.type.GoIRStructType
import org.opentaint.ir.go.type.GoIRType

internal fun GoSerializedCondition?.resolveToRuleCondition(signature: GoFunctionSignature, project: GoIRProgram?): CommonCondition<GoRuleCondition> {
    val resolved = this?.resolveImpl(signature, project) ?: mkTrue()
    return resolved.simplify()
}

private fun GoSerializedCondition.resolveImpl(signature: GoFunctionSignature, project: GoIRProgram?): CommonCondition<GoRuleCondition> = when (this) {
    GoSerializedCondition.True -> mkTrue()

    is GoSerializedCondition.And -> mkAnd(allOf.map { it.resolveImpl(signature, project) })
    is GoSerializedCondition.Or -> mkOr(anyOf.map { it.resolveImpl(signature, project) })
    is GoSerializedCondition.Not -> CommonCondition.Not(not.resolveImpl(signature, project))

    is GoSerializedCondition.ContainsMark -> pos.resolveAny(signature, project, PositionBaseWithModifiers::resolve) {
        GoRuleCondition.ContainsMark(it, tainted)
    }

    is GoSerializedCondition.ContainsMarkOnAnyAccessor -> pos.resolveAny(signature, project, PositionBaseWithModifiers::resolve) {
        GoRuleCondition.ContainsMarkOnAnyAccessor(it, tainted)
    }

    is GoSerializedCondition.ConstantCmp -> {
        val typedValue = value.toTypedConstantValue()
        pos.resolveAny(signature, project, PositionBase::resolve) {
            when (cmp) {
                GoSerializedCondition.ConstantCmpType.Eq -> GoRuleCondition.ConstantEq(it, typedValue)
                GoSerializedCondition.ConstantCmpType.Lt -> GoRuleCondition.ConstantLt(it, typedValue)
                GoSerializedCondition.ConstantCmpType.Gt -> GoRuleCondition.ConstantGt(it, typedValue)
            }
        }
    }

    is GoSerializedCondition.ConstantMatches -> pos.resolveAny(signature, project, PositionBase::resolve) {
        GoRuleCondition.ConstantMatches(it, Regex(pattern))
    }

    is GoSerializedCondition.IsNull -> pos.resolveAny(signature, project, PositionBase::resolve) {
        GoRuleCondition.IsNull(it)
    }

    is GoSerializedCondition.IsConstant -> pos.resolveAny(signature, project, PositionBase::resolve) {
        GoRuleCondition.IsConstant(it)
    }

    is GoSerializedCondition.NumberOfArgs -> if (n == signature.arity) mkTrue() else mkFalse()

    is GoSerializedCondition.IsType -> pos.resolveAny(signature, project, PositionBase::resolve) {
        GoRuleCondition.IsType(typeName, it)
    }
}

private fun <T, R> T.resolveAny(
    signature: GoFunctionSignature,
    project: GoIRProgram?,
    resolve: T.(GoFunctionSignature, GoIRProgram?) -> List<R>,
    body: (R) -> GoRuleCondition
): CommonCondition<GoRuleCondition> =
    mkOr(resolve(signature, project).map { CommonCondition.Atom(body(it)) })

private fun GoSerializedCondition.ConstantValue.toTypedConstantValue(): ConstantValue =
    when (type) {
        GoSerializedCondition.ConstantType.Str -> ConstantStringValue(value)
        GoSerializedCondition.ConstantType.Bool -> ConstantBooleanValue(value.toBoolean())
        GoSerializedCondition.ConstantType.Int -> ConstantIntValue(value.toInt())
    }

fun PositionBase.resolve(signature: GoFunctionSignature, project: GoIRProgram?): List<Position.Simple> = when (this) {
    is PositionBase.AnyArgument -> {
        // todo: any arg classifier
        List(signature.arity) { Position.Argument(it) }
    }

    is PositionBase.Argument -> {
        val i = idx
        if (i == null) {
            List(signature.arity) { Position.Argument(it) }
        } else if (i >= signature.arity) {
            emptyList()
        } else {
            listOf(Position.Argument(i))
        }
    }

    is PositionBase.ClassStatic -> error("Unused")
    is PositionBase.Result -> listOf(Position.Result)
    is PositionBase.This -> if (signature.hasReceiver) listOf(Position.This) else emptyList()
}

fun PositionBaseWithModifiers.resolve(signature: GoFunctionSignature, project: GoIRProgram?): List<Position> {
    val base = base.resolve(signature, project)
    val modifiers = when (this) {
        is PositionBaseWithModifiers.BaseOnly -> return base
        is PositionBaseWithModifiers.WithModifiers -> modifiers
    }

    val accessors = modifiers.resolveUntyped()
    if (accessors != null) {
        return base.map { b -> mkPosition(b, accessors) }
    }

    return base.mapNotNull {
        val type = signature.positionType(it, project)
            ?: return@mapNotNull null

        val accessors = modifiers.resolveWithType(type)
            ?: return@mapNotNull null

        mkPosition(it, accessors)
    }
}

private fun GoFunctionSignature.positionType(pos: Position.Simple, project: GoIRProgram?): GoIRType? {
    val typeName = when (pos) {
        is Position.Argument -> paramTypes.getOrNull(pos.index)
        is Position.Result -> resultType
        is Position.This -> receiverType
    }

    val nonPtrType = typeName?.trimStart('*') ?: return null
    val typePkg = nonPtrType.substringBeforeLast('.', "")
    val simpleTypeName = nonPtrType.substringAfterLast('.')

    return project?.findPackage(typePkg)?.findNamedType(simpleTypeName)?.underlying
}

private fun mkPosition(
    base: Position.Simple,
    accessors: List<PositionAccessor>
): Position = accessors.fold(base as Position) { ac, accessor ->
    PositionWithAccess(ac, accessor)
}

private fun List<PositionModifier>.resolveUntyped(): List<PositionAccessor>? {
    return map { mod ->
        when (mod) {
            is PositionModifier.ArrayElement -> PositionAccessor.ElementAccessor
            is PositionModifier.Field -> {
                if (mod.className.isEmpty()) {
                    return null
                }
                PositionAccessor.FieldAccessor(mod.className, mod.fieldName, mod.fieldType)
            }

            is PositionModifier.AnyField -> error("Unused")
        }
    }
}

private fun List<PositionModifier>.resolveWithType(baseType: GoIRType): List<PositionAccessor>? {
    var type = baseType
    val accessors = mutableListOf<PositionAccessor>()
    for (mod in this) {
        when (mod) {
            is PositionModifier.ArrayElement -> {
                if (type !is GoIRArrayType) return null
                accessors += PositionAccessor.ElementAccessor

                type = type.elem
            }

            is PositionModifier.Field -> {
                if (type !is GoIRStructType) return null
                val field = type.fields.firstOrNull { it.name == mod.fieldName } ?: return null

                val structName = type.namedType?.fullName ?: return null
                accessors += PositionAccessor.FieldAccessor(structName, field.name, field.type.typeName)

                type = field.type
            }

            is PositionModifier.AnyField -> error("Unused")
        }
    }
    return accessors
}
