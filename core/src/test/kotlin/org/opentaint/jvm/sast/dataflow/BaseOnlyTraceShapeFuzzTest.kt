package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class BaseOnlyTraceShapeFuzzTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"
    override val useDefaultUnrollStrategy: Boolean = true

    private val testClass = "test.samples.BaseOnlyTraceShapeFuzzSample"
    private val ruleId = "base-only-trace-shape-fuzz"
    private val mark = "trace-shape-taint"
    private val probeMark = "trace-shape-probe"
    private val probeResultMark = "trace-shape-probe-result"

    private val config = SerializedTaintConfig(
        source = listOf(
            sourceRule(testClass, "source", mark),
            sourceRule(testClass, "source", probeMark),
            SerializedRule.Source(
                function = functionMatcher(testClass, "probe"),
                condition = SerializedCondition.ContainsMark(
                    probeMark,
                    PositionBaseWithModifiers.BaseOnly(Argument(0)),
                ),
                taint = listOf(
                    SerializedTaintAssignAction(
                        kind = probeResultMark,
                        pos = PositionBaseWithModifiers.BaseOnly(PositionBase.Result),
                    ),
                ),
            ),
        ),
        sink = listOf(
            SerializedRule.Sink(
                function = functionMatcher(testClass, "sink"),
                condition = SerializedCondition.ContainsMark(mark, responseBody(Argument(0))),
                id = ruleId,
            ),
        ),
    )

    @TestFactory
    fun `BaseOnly resolves traces through field abstract summaries`(): List<DynamicTest> =
        samples.map { method ->
            DynamicTest.dynamicTest(method) {
                assertReachable(config, testClass, method, ruleId, "$method Tree control", ApMode.Tree)
                assertReachable(config, testClass, method, ruleId, "$method BaseOnly", ApMode.BaseOnlyField)
            }
        }

    private fun responseBody(position: PositionBase) = PositionBaseWithModifiers.WithModifiers(
        position,
        listOf(PositionModifier.Field("$testClass\$Response", "body", "$testClass\$Token")),
    )

    private companion object {
        val samples = listOf(
            "projectedProbedFactory",
            "projectedProbedConstructorFactory",
            "projectedDoubleProbedFactory",
            "projectedRelayedProbeFactory",
        )
    }
}
