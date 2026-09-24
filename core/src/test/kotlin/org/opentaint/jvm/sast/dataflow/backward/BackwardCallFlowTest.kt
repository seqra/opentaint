package org.opentaint.jvm.sast.dataflow.backward

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintCleanAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintPassAction

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BackwardCallFlowTest : BackwardAnalysisTest() {
    companion object {
        private const val SAMPLE_PACKAGE = "test.samples"
        private const val CALL_CLS = "$SAMPLE_PACKAGE.BackwardCallSample"
        private const val STRING_CLS = "$SAMPLE_PACKAGE.StringMethodDataFlowSample"
        private const val TAINT_MARK = "tainted"
        private const val OTHER_MARK = "other"
        private const val TRANSFORMED_MARK = "transformed"
        private const val RULE_ID = "backward-call-rule"
    }

    override val sourceFileExtension: String = "java"
    override val useDefaultConfig: Boolean = true

    private fun config(
        cls: String,
        sinkMark: String = TAINT_MARK,
        sources: List<SerializedRule.Source> = listOf(sourceRule(cls, "source", TAINT_MARK)),
        passThrough: List<SerializedRule.PassThrough>? = null,
        cleaner: List<SerializedRule.Cleaner>? = null,
    ) = SerializedTaintConfig(
        source = sources,
        sink = listOf(sinkRule(cls, "sink", RULE_ID, listOf(Argument(0) to sinkMark))),
        passThrough = passThrough,
        cleaner = cleaner,
    )

    private fun cleanerRule(fqn: String, method: String, position: PositionBase, mark: String?) =
        SerializedRule.Cleaner(
            function = functionMatcher(fqn, method),
            cleans = listOf(
                SerializedTaintCleanAction(taintKind = mark, pos = PositionBaseWithModifiers.BaseOnly(position))
            )
        )

    private fun stripCopyMarkRule(mark: String) = SerializedRule.PassThrough(
        function = functionMatcher("java.lang.String", "strip"),
        copy = listOf(
            SerializedTaintPassAction(
                taintKind = mark,
                from = PositionBaseWithModifiers.BaseOnly(PositionBase.This),
                to = PositionBaseWithModifiers.BaseOnly(PositionBase.Result),
            )
        )
    )

    private fun assertReached(config: SerializedTaintConfig, cls: String, method: String, sourceMethod: String = "source") =
        assertSourceReached(config, cls, method, sourceMethod, TAINT_MARK, method)

    private fun assertNotReached(config: SerializedTaintConfig, cls: String, method: String) =
        assertNoSourceReached(config, cls, method, method)

    @Test
    fun `direct call - sink argument is the source result`() {
        assertReached(config(CALL_CLS), CALL_CLS, "directCall")
    }

    @Test
    fun `direct call - finding is recorded at the source call in the entry method`() {
        val result = runBackwardAnalysis(config(CALL_CLS), CALL_CLS, "directCall")
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status)

        val finding = result.reachedSources("source", TAINT_MARK).singleOrNull()
            ?: error("expected exactly one source finding, got ${result.sourceFindings}")
        assertEquals("directCall", finding.statement.location.method.name)
    }

    @Test
    fun `negative - sink argument comes from an unrelated call`() {
        assertNotReached(config(CALL_CLS), CALL_CLS, "noSourceCall")
    }

    @Test
    fun `negative - sink demands a mark the source does not produce`() {
        assertNotReached(config(CALL_CLS, sinkMark = OTHER_MARK), CALL_CLS, "directCall")
    }

    @Test
    fun `library pass-through - default concat rule maps the result demand to the receiver`() {
        assertReached(config(CALL_CLS), CALL_CLS, "libraryConcat")
    }

    @Test
    fun `library pass-through - default string rules`() {
        for (method in listOf("substringFlow", "toLowerCaseFlow", "trimFlow", "concatFlow", "replaceFlow")) {
            assertReached(config(STRING_CLS), STRING_CLS, method)
        }
    }

    @Test
    fun `library pass-through - string builder receiver demand reaches the appended value`() {
        assertReached(config(CALL_CLS), CALL_CLS, "libraryStringBuilder")
    }

    @Test
    fun `negative - string builder receives only an untainted value`() {
        assertNotReached(config(CALL_CLS), CALL_CLS, "libraryStringBuilderOtherValue")
    }

    @Test
    fun `library pass-through - copy mark rule inverts for its mark`() {
        assertReached(config(CALL_CLS, passThrough = listOf(stripCopyMarkRule(TAINT_MARK))), CALL_CLS, "libraryCopyMark")
    }

    @Test
    fun `negative - copy mark rule does not invert for another mark`() {
        assertNotReached(config(CALL_CLS, passThrough = listOf(stripCopyMarkRule(OTHER_MARK))), CALL_CLS, "libraryCopyMark")
    }

    @Test
    fun `negative - unresolved call without pass rules kills the result demand`() {
        assertNotReached(config(CALL_CLS), CALL_CLS, "libraryCopyMark")
    }

    @Test
    fun `callee heap effect - argument demand is summarised and reaches the source inside the callee`() {
        val result = runBackwardAnalysis(config(CALL_CLS), CALL_CLS, "calleeArgHeapEffect")
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status)

        val findings = result.reachedSources("source", TAINT_MARK)
        assertTrue(
            findings.any { it.statement.location.method.name == "fill" },
            "expected the source call inside fill to be reached, got ${result.sourceFindings}"
        )
    }

    @Test
    fun `negative - callee heap effect on another argument`() {
        assertNotReached(config(CALL_CLS), CALL_CLS, "calleeArgHeapEffectOtherArg")
    }

    @Disabled("needs the sequent flow function for `return value` in the callee")
    @Test
    fun `callee return value - result demand enters the callee and reaches the caller source`() {
        assertReached(config(CALL_CLS), CALL_CLS, "calleeReturnValue")
    }

    @Test
    fun `cleaner - argument cleaner drops the demand`() {
        val cleaner = listOf(cleanerRule(CALL_CLS, "sanitize", Argument(0), TAINT_MARK))
        assertNotReached(config(CALL_CLS, cleaner = cleaner), CALL_CLS, "cleanedArgument")
    }

    @Test
    fun `cleaner - argument demand passes a cleaner of another mark`() {
        val cleaner = listOf(cleanerRule(CALL_CLS, "sanitize", Argument(0), OTHER_MARK))
        assertReached(config(CALL_CLS, cleaner = cleaner), CALL_CLS, "cleanedArgument")
    }

    @Test
    fun `cleaner - demand passes a call without cleaner`() {
        assertReached(config(CALL_CLS), CALL_CLS, "cleanedArgument")
    }

    @Test
    fun `cleaner - remove all marks on the result drops the library result demand`() {
        val cleaner = listOf(cleanerRule("java.lang.String", "trim", PositionBase.Result, mark = null))
        assertNotReached(config(CALL_CLS, cleaner = cleaner), CALL_CLS, "cleanedResult")
    }

    @Test
    fun `cleaner - receiver cleaner drops the pass-through generated demand`() {
        val cleaner = listOf(cleanerRule("java.lang.String", "trim", PositionBase.This, TAINT_MARK))
        assertNotReached(config(CALL_CLS, cleaner = cleaner), CALL_CLS, "cleanedResult")
    }

    @Test
    fun `cleaner - library result demand without cleaner reaches the source`() {
        assertReached(config(CALL_CLS), CALL_CLS, "cleanedResult")
    }

    @Test
    fun `conditional source - source condition becomes a demand on the argument`() {
        val sources = listOf(
            sourceRule(CALL_CLS, "source", TAINT_MARK),
            sourceRule(CALL_CLS, "transform", TRANSFORMED_MARK, condition = listOf(Argument(0) to TAINT_MARK)),
        )
        val config = config(CALL_CLS, sinkMark = TRANSFORMED_MARK, sources = sources)

        val result = runBackwardAnalysis(config, CALL_CLS, "conditionalSource")
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status)
        assertTrue(
            result.reachedSources("source", TAINT_MARK).isNotEmpty(),
            "expected the transform condition demand to reach source, got ${result.sourceFindings}"
        )
        assertTrue(
            result.reachedSources("transform", TRANSFORMED_MARK).isEmpty(),
            "a conditional source must not be reported as found, got ${result.sourceFindings}"
        )
    }

    @Test
    fun `unconditional source - source on the sink argument path is found for its own mark`() {
        val sources = listOf(sourceRule(CALL_CLS, "transform", TRANSFORMED_MARK))
        val config = config(CALL_CLS, sinkMark = TRANSFORMED_MARK, sources = sources)

        val result = runBackwardAnalysis(config, CALL_CLS, "conditionalSource")
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status)
        assertTrue(
            result.reachedSources("transform", TRANSFORMED_MARK).isNotEmpty(),
            "expected transform to be found, got ${result.sourceFindings}"
        )
    }
}
