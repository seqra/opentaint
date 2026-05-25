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

internal fun GoSerializedCondition?.resolveToRuleCondition(signature: GoFunctionSignature): CommonCondition<GoRuleCondition> {
    val resolved = this?.resolveImpl(signature) ?: mkTrue()
    return resolved.simplify()
}

private fun GoSerializedCondition.resolveImpl(signature: GoFunctionSignature): CommonCondition<GoRuleCondition> = when (this) {
    GoSerializedCondition.True -> mkTrue()

    is GoSerializedCondition.And -> mkAnd(allOf.map { it.resolveImpl(signature) })
    is GoSerializedCondition.Or -> mkOr(anyOf.map { it.resolveImpl(signature) })
    is GoSerializedCondition.Not -> CommonCondition.Not(not.resolveImpl(signature))

    is GoSerializedCondition.ContainsMark -> pos.resolveAny(signature, PositionBaseWithModifiers::resolve) {
        GoRuleCondition.ContainsMark(it, tainted)
    }

    is GoSerializedCondition.ConstantCmp -> {
        val typedValue = value.toTypedConstantValue()
        pos.resolveAny(signature, PositionBase::resolve) {
            when (cmp) {
                GoSerializedCondition.ConstantCmpType.Eq -> GoRuleCondition.ConstantEq(it, typedValue)
                GoSerializedCondition.ConstantCmpType.Lt -> GoRuleCondition.ConstantLt(it, typedValue)
                GoSerializedCondition.ConstantCmpType.Gt -> GoRuleCondition.ConstantGt(it, typedValue)
            }
        }
    }

    is GoSerializedCondition.ConstantMatches -> pos.resolveAny(signature, PositionBase::resolve) {
        GoRuleCondition.ConstantMatches(it, Regex(pattern))
    }

    is GoSerializedCondition.IsNull -> pos.resolveAny(signature, PositionBase::resolve) {
        GoRuleCondition.IsNull(it)
    }

    is GoSerializedCondition.IsConstant -> pos.resolveAny(signature, PositionBase::resolve) {
        GoRuleCondition.IsConstant(it)
    }

    is GoSerializedCondition.NumberOfArgs -> if (n == signature.numArgs) mkTrue() else mkFalse()

    is GoSerializedCondition.IsType -> pos.resolveAny(signature, PositionBase::resolve) {
        GoRuleCondition.IsType(typeName, it)
    }
}

private fun <T, R> T.resolveAny(
    signature: GoFunctionSignature,
    resolve: T.(GoFunctionSignature) -> List<R>,
    body: (R) -> GoRuleCondition
): CommonCondition<GoRuleCondition> =
    mkOr(resolve(signature).map { CommonCondition.Atom(body(it)) })

private fun GoSerializedCondition.ConstantValue.toTypedConstantValue(): ConstantValue =
    when (type) {
        GoSerializedCondition.ConstantType.Str -> ConstantStringValue(value)
        GoSerializedCondition.ConstantType.Bool -> ConstantBooleanValue(value.toBoolean())
        GoSerializedCondition.ConstantType.Int -> ConstantIntValue(value.toInt())
    }

fun PositionBase.resolve(signature: GoFunctionSignature): List<Position.Simple> = when (this) {
    is PositionBase.AnyArgument -> {
        // todo: any arg classifier
        List(signature.numArgs) { Position.Argument(it) }
    }

    is PositionBase.Argument -> {
        val i = idx
        if (i == null) {
            List(signature.numArgs) { Position.Argument(it) }
        } else if (i > signature.numArgs) {
            emptyList()
        } else {
            listOf(Position.Argument(i))
        }
    }

    is PositionBase.ClassStatic -> error("Unused")
    is PositionBase.Result -> listOf(Position.Result)
    is PositionBase.This -> if (signature.hasReceiver) listOf(Position.This) else emptyList()
}

fun PositionBaseWithModifiers.resolve(signature: GoFunctionSignature): List<Position> {
    val base = base.resolve(signature)
    val accessors = when (this) {
        is PositionBaseWithModifiers.BaseOnly -> return base
        is PositionBaseWithModifiers.WithModifiers -> modifiers.map { mod ->
            when (mod) {
                is PositionModifier.ArrayElement -> PositionAccessor.ElementAccessor
                is PositionModifier.Field -> PositionAccessor.FieldAccessor(mod.className, mod.fieldName, mod.fieldType)
                is PositionModifier.AnyField -> error("Unused")
            }
        }
    }

    return base.map { b ->
        accessors.fold(b as Position) { ac, accessor ->
            PositionWithAccess(ac, accessor)
        }
    }
}
