package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedAssignAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedGlobalSource
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Result
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers.WithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier.ArrayElement
import kotlin.test.Test
import kotlin.test.assertTrue

/**
 * Tests that GlobalReadSource rules produce vulnerabilities whose traces
 * resolve. Without Task B's SequentSource precondition, the trace resolver
 * cannot explain how the global-read source-fact was generated, and the
 * vulnerability is filtered out by the `.trace != null` gate.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GlobalSourceTraceTest : AnalysisTest() {

    private val osArgsGlobalSource = GoSerializedGlobalSource(
        pkg = GoNameMatcher.Simple("os"),
        global = GoNameMatcher.Simple("Args"),
        condition = null,
        taint = listOf(GoSerializedAssignAction("taint", WithModifiers(Result, listOf(ArrayElement)))),
        info = null,
    )

    @Test
    fun globalSource001T() {
        val vulns = runAnalysisWithGlobalSource(osArgsGlobalSource, stdSink, "test.globalSource001T")
        assertTrue(vulns.isNotEmpty(), "expected at least one traced vuln from os.Args -> util.Sink")
    }

    @Test
    fun globalSource002F() {
        val vulns = runAnalysisWithGlobalSource(osArgsGlobalSource, stdSink, "test.globalSource002F")
        assertTrue(vulns.isEmpty(), "did not expect any vuln when sink receives a literal")
    }
}
