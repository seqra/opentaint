package org.opentaint.semgrep.pattern.conversion.python

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.python.serialized.PIRUserDefinedRuleInfo
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCondition
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonRule
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintAssignAction
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintCleanAction
import org.opentaint.semgrep.pattern.MetaVarConstraint
import org.opentaint.semgrep.pattern.UserRuleFromSemgrepInfo
import org.opentaint.semgrep.pattern.PlaceholderMethodName
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.PythonConcreteType
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureName
import org.opentaint.semgrep.pattern.conversion.TypeConstraint
import org.opentaint.semgrep.pattern.conversion.taint.MetaVarConstraintOrPlaceHolder
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleGenerationCtx
import org.opentaint.semgrep.pattern.toDNF

typealias PythonTaintRuleGenerationCtx =
    TaintRuleGenerationCtx<SerializedPythonRule, SerializedPythonCondition, SerializedPythonTaintAssignAction, SerializedPythonTaintCleanAction>

data class PythonUserRuleFromSemgrepInfo(
    val ruleId: String,
    override val relevantTaintMarks: Set<String>,
) : PIRUserDefinedRuleInfo

fun UserRuleFromSemgrepInfo.toPython() = PythonUserRuleFromSemgrepInfo(ruleId, relevantTaintMarks)

internal data class PythonRuleConditionData(
    val function: String,
    val condition: SerializedPythonCondition,
)

internal class PythonRuleConditionBuilder {
    var function: String? = null
    val conditions = mutableListOf<SerializedPythonCondition>()

    fun build(): PythonRuleConditionData = PythonRuleConditionData(
        function = function ?: ANY_PYTHON_FUNCTION,
        condition = pythonAnd(conditions),
    )
}

internal data class PythonEvaluatedEdgeCondition(
    val ruleCondition: PythonRuleConditionData,
    val accessedVarPosition: Map<MetavarAtom, PythonRegisterVarPosition>,
)

internal data class PythonRegisterVarPosition(
    val varName: MetavarAtom,
    val positions: MutableSet<PositionBase>,
)

/**
 * Collapses a method signature into the single dotted `function` string of a [PythonTarget.Function].
 * Python resolves calls by qualified name, so the enclosing dotted path (when concrete)
 * and the method name fold into one string. An instance call (`$X.method(...)`) has no enclosing name
 * and yields the short method name, which the resolver matches against the callee's trailing segment.
 */
internal fun PythonTaintRuleGenerationCtx.evaluatePythonFunctionNames(
    methodName: SignatureName,
    enclosing: TypeConstraint,
    trace: SemgrepRuleLoadStepTrace,
): List<String> {
    val prefix = (enclosing as? TypeConstraint.Concrete)?.let { (it.type as? PythonConcreteType.Named)?.name }
    return when (methodName) {
        SignatureName.AnyName -> listOf(combinePythonFunctionName(prefix, ANY_PYTHON_FUNCTION, isRegex = true))
        is SignatureName.Concrete -> listOf(combinePythonFunctionName(prefix, methodName.name, isRegex = false))
        is SignatureName.MetaVar -> {
            val constraint = when (val c = metaVarInfo.constraints[methodName.metaVar]) {
                null -> null
                is MetaVarConstraintOrPlaceHolder.Constraint -> c.constraint
                is MetaVarConstraintOrPlaceHolder.PlaceHolder -> {
                    trace.error(PlaceholderMethodName())
                    c.constraint
                }
            }

            if (constraint == null) {
                return listOf(combinePythonFunctionName(prefix, ANY_PYTHON_FUNCTION, isRegex = true))
            }

            constraint.constraint.toDNF().mapNotNull { cube ->
                // A single positive concrete/regex per cube; negations and disjuncts within a
                // name aren't representable as one function matcher, so drop them.
                if (cube.negative.isNotEmpty() || cube.positive.size != 1) return@mapNotNull null
                when (val c = cube.positive.single().constraint) {
                    is MetaVarConstraint.Concrete -> combinePythonFunctionName(prefix, c.value, isRegex = false)
                    is MetaVarConstraint.RegExp -> combinePythonFunctionName(prefix, c.regex, isRegex = true)
                }
            }.ifEmpty { listOf(combinePythonFunctionName(prefix, ANY_PYTHON_FUNCTION, isRegex = true)) }
        }
    }
}

private fun combinePythonFunctionName(prefix: String?, name: String, isRegex: Boolean): String = when {
    prefix == null -> name
    !isRegex -> "$prefix.$name"
    // A regex name combined with a concrete prefix must stay a single regex matched against the
    // qualified callee, so escape the prefix's dots.
    else -> "${prefix.replace(".", "\\.")}\\.$name"
}
