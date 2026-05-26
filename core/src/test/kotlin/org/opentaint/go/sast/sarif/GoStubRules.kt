package org.opentaint.go.sast.sarif

import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedAssignAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCondition
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.dataflow.configuration.go.serialized.GoSinkMetaData
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider

object GoStubRules {
    const val TAINT_MARK: String = "taint"

    const val SINK_RULE_ID: String = "go-taint-sink"

    val defaultSources: List<GoSerializedRule.Source> = listOf(
        GoSerializedRule.Source(
            function = GoNameMatcher.Simple("test/util.Source"),
            condition = null,
            taint = listOf(
                GoSerializedAssignAction(TAINT_MARK, PositionBaseWithModifiers.BaseOnly(PositionBase.Result)),
            ),
            info = null
        ),
    )

    val defaultSinks: List<GoSerializedRule.Sink> = listOf(
        GoSerializedRule.Sink(
            function = GoNameMatcher.Simple("test/util.Sink"),
            condition = GoSerializedCondition.ContainsMark(
                TAINT_MARK,
                PositionBaseWithModifiers.BaseOnly(PositionBase.Argument(0)),
            ),
            trackFactsReachAnalysisEnd = emptyList(),
            id = SINK_RULE_ID,
            meta = GoSinkMetaData("Taint sink: test/util.Sink"),
            info = null
        ),
    )

    fun defaultConfig(): GoTaintRulesProvider {
        val serializedConfig = GoSerializedTaintConfig(
            source = defaultSources,
            sink = defaultSinks,
        )

        val config = GoTaintConfiguration()
        config.loadConfig(serializedConfig)
        return config
    }
}