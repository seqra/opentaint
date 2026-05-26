package org.opentaint.semgrep.pattern.conversion.go

import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCondition
import org.opentaint.dataflow.configuration.go.serialized.GoUserDefinedRuleInfo
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.semgrep.pattern.UserRuleFromSemgrepInfo
import org.opentaint.semgrep.pattern.conversion.MetavarAtom

data class GoUserRuleFromSemgrepInfo(
    val ruleId: String,
    override val relevantTaintMarks: Set<String>
) : GoUserDefinedRuleInfo

fun UserRuleFromSemgrepInfo.toGo() =
    GoUserRuleFromSemgrepInfo(ruleId, relevantTaintMarks)

internal data class GoRuleConditionData(
    val function: GoNameMatcher,
    val condition: GoSerializedCondition,
)

internal class GoRuleConditionBuilder {
    var function: GoNameMatcher? = null
    val conditions = hashSetOf<GoSerializedCondition>()

    fun build(): GoRuleConditionData = GoRuleConditionData(
        function = function ?: goAnyFunction(),
        condition = GoSerializedCondition.and(conditions.toList()),
    )
}

internal data class GoEvaluatedEdgeCondition(
    val ruleCondition: GoRuleConditionData,
    val accessedVarPosition: Map<MetavarAtom, GoRegisterVarPosition>,
)

internal data class GoRegisterVarPosition(
    val varName: MetavarAtom,
    val positions: MutableSet<PositionBaseWithModifiers>,
)
