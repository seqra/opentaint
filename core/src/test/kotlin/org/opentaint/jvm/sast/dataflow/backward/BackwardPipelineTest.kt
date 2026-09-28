package org.opentaint.jvm.sast.dataflow.backward

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.opentaint.common.sast.dataflow.AnalysisDirection
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintCleanAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintPassAction
import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.dataflow.configuration.jvm.serialized.UserDefinedRuleInfo
import org.opentaint.jvm.sast.dataflow.AnalysisTest

class BackwardPipelineTest : AnalysisTest() {
    private companion object {
        const val CLS = "test.samples.BackwardPipelineSample"
        const val LAMBDA_CLS = "test.samples.LambdaDataFlowSample"
        const val MARK = "tainted"
        const val DONE = "done"
        const val WRAPPED = "wrapped"
        const val STATE = "state"
        const val STATE_VAR = "backward.pipeline.state"
        const val MODELLED = "modelled"
    }

    private data class CleanerRuleInfo(override val relevantTaintMarks: Set<String>) : UserDefinedRuleInfo

    override val sourceFileExtension: String = "java"

    private fun ids(config: SerializedTaintConfig, entry: String, direction: AnalysisDirection, cls: String = CLS) =
        runAnalysis(config, cls, entry, direction).mapTo(hashSetOf()) { it.vulnerability.rule.id }

    private fun assertBothDirections(config: SerializedTaintConfig, entry: String, expected: Set<String>, cls: String = CLS) {
        assertEquals(expected, ids(config, entry, AnalysisDirection.FORWARD, cls), "$entry: forward")
        assertEquals(expected, ids(config, entry, AnalysisDirection.BACKWARD, cls), "$entry: backward")
    }

    private fun markSink(method: String, id: String, trackFacts: List<SerializedTaintAssignAction> = emptyList()) =
        SerializedRule.Sink(
            function = functionMatcher(CLS, method),
            condition = SerializedCondition.ContainsMark(MARK, PositionBaseWithModifiers.BaseOnly(Argument(0))),
            trackFactsReachAnalysisEnd = trackFacts,
            id = id,
            meta = SinkMetaData(note = id),
        )

    private fun cleaner(method: String, mark: String, position: PositionBase) = SerializedRule.Cleaner(
        function = functionMatcher(CLS, method),
        cleans = listOf(SerializedTaintCleanAction(taintKind = mark, pos = PositionBaseWithModifiers.BaseOnly(position))),
        info = CleanerRuleInfo(setOf(mark)),
    )

    private val sharedMarkConfig = SerializedTaintConfig(
        source = listOf(sourceRule(CLS, "source", MARK)),
        sink = listOf(markSink("sinkA", "sink-a"), markSink("sinkB", "sink-b")),
    )

    private val localRequirementConfig = SerializedTaintConfig(
        source = listOf(sourceRule(CLS, "source", MARK)),
        cleaner = listOf(cleaner("finish", DONE, Argument(0))),
        sink = listOf(
            markSink(
                "sinkA", "sink-a",
                listOf(SerializedTaintAssignAction(kind = DONE, pos = PositionBaseWithModifiers.BaseOnly(Argument(0))))
            )
        ),
    )

    private val staticRequirementConfig = SerializedTaintConfig(
        source = listOf(sourceRule(CLS, "source", MARK)),
        cleaner = listOf(cleaner("finishState", STATE, PositionBase.ClassStatic(STATE_VAR))),
        sink = listOf(
            markSink(
                "sinkA", "sink-a",
                listOf(
                    SerializedTaintAssignAction(
                        kind = STATE,
                        pos = PositionBaseWithModifiers.BaseOnly(PositionBase.ClassStatic(STATE_VAR))
                    )
                )
            )
        ),
    )

    @Test
    fun `sinks sharing a mark are attributed separately`() {
        assertBothDirections(sharedMarkConfig, "sharedMarkOneReached", setOf("sink-a"))
        assertBothDirections(sharedMarkConfig, "sharedMarkBothReached", setOf("sink-a", "sink-b"))
    }

    @Test
    fun `local end requirement is dropped by a cleaner after the sink`() {
        assertBothDirections(localRequirementConfig, "localRequirementCleaned", emptySet())
        assertBothDirections(localRequirementConfig, "localRequirementCleanedInCallee", emptySet())
        assertBothDirections(localRequirementConfig, "localRequirementKept", setOf("sink-a"))
    }

    @Test
    fun `static end requirement is dropped by a cleaner after the sink`() {
        assertBothDirections(staticRequirementConfig, "staticRequirementCleaned", emptySet())
        assertBothDirections(staticRequirementConfig, "staticRequirementCleanedInCallee", emptySet())
        assertBothDirections(staticRequirementConfig, "staticRequirementKept", setOf("sink-a"))
    }

    @Test
    fun `conditional source inside a callee reached from the caller`() {
        val config = SerializedTaintConfig(
            source = listOf(
                sourceRule(CLS, "source", MARK),
                sourceRule(CLS, "wrap", WRAPPED, condition = listOf(Argument(0) to MARK)),
            ),
            sink = listOf(sinkRule(CLS, "sinkWrapped", "sink-wrapped", listOf(Argument(0) to WRAPPED))),
        )
        assertBothDirections(config, "conditionalSourceInCallee", setOf("sink-wrapped"))
    }

    private fun modellingSource(fqn: String, method: String, info: UserDefinedRuleInfo?) = SerializedRule.Source(
        function = functionMatcher(fqn, method),
        taint = listOf(SerializedTaintAssignAction(kind = MODELLED, pos = PositionBaseWithModifiers.BaseOnly(PositionBase.Result))),
        info = info,
    )

    private fun userRuleConfig(fqn: String, method: String, info: UserDefinedRuleInfo?) = SerializedTaintConfig(
        source = listOf(sourceRule(CLS, "source", MARK), modellingSource(fqn, method, info)),
        sink = listOf(markSink("sinkA", "sink-a")),
        passThrough = listOf(
            SerializedRule.PassThrough(
                function = functionMatcher("java.lang.String", "trim"),
                copy = listOf(
                    SerializedTaintPassAction(
                        from = PositionBaseWithModifiers.BaseOnly(PositionBase.This),
                        to = PositionBaseWithModifiers.BaseOnly(PositionBase.Result),
                    )
                ),
            )
        ),
    )

    @Test
    fun `user rule on a resolved callee drops the mark from its summary`() {
        assertBothDirections(userRuleConfig(CLS, "modelled", CleanerRuleInfo(setOf(MARK))), "userRuleOnResolvedCallee", emptySet())
        assertBothDirections(userRuleConfig(CLS, "modelled", info = null), "userRuleOnResolvedCallee", setOf("sink-a"))
    }

    @Test
    fun `user rule on an unresolved callee drops the mark from its pass-through`() {
        val info = CleanerRuleInfo(setOf(MARK))
        assertBothDirections(userRuleConfig("java.lang.String", "trim", info), "userRuleOnUnresolvedCallee", emptySet())
        assertBothDirections(userRuleConfig("java.lang.String", "trim", info = null), "userRuleOnUnresolvedCallee", setOf("sink-a"))
    }

    @Test
    fun `method exit sinks fire only on facts created below the method`() {
        val config = SerializedTaintConfig(
            source = listOf(sourceRule(CLS, "source", MARK)),
            methodExitSink = listOf(
                methodExitSinkRule(CLS, "exitHelper", "exit-sink", MARK),
                methodExitSinkRule(CLS, "exitHelperWithSource", "exit-sink", MARK),
            ),
        )
        assertBothDirections(config, "exitSinkSourceInCaller", emptySet())
        assertBothDirections(config, "exitSinkSourceInside", setOf("exit-sink"))
    }

    @Test
    fun `entry source on a static state variable reaches a sink in the method`() {
        val statePosition = PositionBaseWithModifiers.BaseOnly(PositionBase.ClassStatic(STATE_VAR))
        val config = SerializedTaintConfig(
            entryPoint = listOf(
                SerializedRule.EntryPoint(
                    function = functionMatcher(CLS, "withState"),
                    taint = listOf(SerializedTaintAssignAction(kind = STATE, pos = statePosition)),
                )
            ),
            sink = listOf(
                SerializedRule.Sink(
                    function = functionMatcher(CLS, "sinkA"),
                    condition = SerializedCondition.ContainsMark(STATE, statePosition),
                    id = "state-sink",
                    meta = SinkMetaData(note = "state-sink"),
                )
            ),
        )
        assertBothDirections(config, "entryStateSource", setOf("state-sink"))
    }

    @Test
    fun `lambda calls resolve to the lambdas registered by the forward prescan`() {
        val config = SerializedTaintConfig(
            source = listOf(sourceRule(LAMBDA_CLS, "source", MARK)),
            sink = listOf(sinkRule(LAMBDA_CLS, "sink", "lambda-rule", listOf(Argument(0) to MARK))),
        )
        assertBothDirections(config, "lambdaCaptureFlow", setOf("lambda-rule"), LAMBDA_CLS)
    }
}
