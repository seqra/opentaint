package org.opentaint.semgrep.pattern.conversion.python

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.python.serialized.PythonPosition
import org.opentaint.dataflow.configuration.python.serialized.PythonPositionBase
import org.opentaint.dataflow.configuration.python.serialized.PythonPositionModifier
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCondition
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintAssignAction
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintCleanAction
import org.opentaint.semgrep.pattern.Mark.GeneratedMark
import org.opentaint.semgrep.pattern.conversion.PythonLanguageStrategy

/** Match-anything function target. */
internal const val ANY_PYTHON_FUNCTION = ".*"

// And-of-nothing is true and Or-of-nothing is false — honored by the runtime's
// RuleConditionRewriter (empty arg lists rewrite to the default true/false expr).
internal val PYTHON_TRUE: SerializedPythonCondition = SerializedPythonCondition.And(emptyList())
internal val PYTHON_FALSE: SerializedPythonCondition = SerializedPythonCondition.Or(emptyList())

internal fun pythonAnd(args: List<SerializedPythonCondition>): SerializedPythonCondition {
    val flat = mutableListOf<SerializedPythonCondition>()
    for (a in args) {
        when {
            a == PYTHON_FALSE -> return PYTHON_FALSE
            a == PYTHON_TRUE -> {}
            a is SerializedPythonCondition.And -> flat += a.allOf
            else -> flat += a
        }
    }
    return if (flat.size == 1) flat.single() else SerializedPythonCondition.And(flat)
}

internal fun pythonOr(args: List<SerializedPythonCondition>): SerializedPythonCondition {
    val flat = mutableListOf<SerializedPythonCondition>()
    for (a in args) {
        when {
            a == PYTHON_TRUE -> return PYTHON_TRUE
            a == PYTHON_FALSE -> {}
            a is SerializedPythonCondition.Or -> flat += a.anyOf
            else -> flat += a
        }
    }
    return if (flat.size == 1) flat.single() else SerializedPythonCondition.Or(flat)
}

/** Drops a trivially-true condition to `null` (the rule's "no condition" form). */
internal fun SerializedPythonCondition.nullIfTrue(): SerializedPythonCondition? = takeUnless { it == PYTHON_TRUE }

/**
 * Maps the language-agnostic [PositionBaseWithModifiers] (produced by the shared rule-generation
 * context) onto the Python serialized position vocabulary.
 */
internal fun PositionBaseWithModifiers.toPythonPosition(): PythonPosition = when (this) {
    is PositionBaseWithModifiers.BaseOnly -> PythonPosition.BaseOnly(base.toPythonPositionBase())
    is PositionBaseWithModifiers.WithModifiers ->
        PythonPosition.WithModifiers(base.toPythonPositionBase(), modifiers.map { it.toPythonPositionModifier() })
}

private fun PositionBase.toPythonPositionBase(): PythonPositionBase = when (this) {
    is PositionBase.Argument -> PythonPositionBase.Argument(idx)
    is PositionBase.AnyArgument ->
        PythonLanguageStrategy.kwargClassifierNameOrNull(classifier)?.let { PythonPositionBase.KwArgument(it) }
            ?: PythonPositionBase.Argument(null)
    PositionBase.This -> PythonPositionBase.This
    PositionBase.Result -> PythonPositionBase.Result
    is PositionBase.ClassStatic -> PythonPositionBase.ClassRef(className)
}

private fun PositionModifier.toPythonPositionModifier(): PythonPositionModifier = when (this) {
    PositionModifier.ArrayElement -> PythonPositionModifier.ArrayElement
    is PositionModifier.Field -> PythonPositionModifier.Field(fieldName)
    // The Python converter never emits attribute loads, so an any-field modifier shouldn't reach here.
    PositionModifier.AnyField -> error("Python rules have no any-field position modifier")
}

internal fun GeneratedMark.mkPythonContainsMark(pos: PositionBaseWithModifiers): SerializedPythonCondition.ContainsMark =
    SerializedPythonCondition.ContainsMark(taintMarkStr(), pos.toPythonPosition())

internal fun GeneratedMark.mkPythonContainsMarkOnAnyAccessor(pos: PositionBaseWithModifiers): SerializedPythonCondition.ContainsMarkOnAnyAccessor =
    SerializedPythonCondition.ContainsMarkOnAnyAccessor(taintMarkStr(), pos.toPythonPosition())

internal fun GeneratedMark.mkPythonAssignMark(pos: PositionBaseWithModifiers): SerializedPythonTaintAssignAction =
    SerializedPythonTaintAssignAction(kind = taintMarkStr(), pos = pos.toPythonPosition())

internal fun GeneratedMark.mkPythonCleanMark(pos: PositionBaseWithModifiers): SerializedPythonTaintCleanAction =
    SerializedPythonTaintCleanAction(taintKind = taintMarkStr(), pos = pos.toPythonPosition())
