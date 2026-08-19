package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.ap.ifds.trace.path.ResolvedInterProceduralTrace
import org.opentaint.dataflow.ap.ifds.trace.path.ResolvedInterProceduralTraceEntry
import org.opentaint.dataflow.ap.ifds.trace.path.TracePathGenerationResult
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class BaseOnlySummaryFieldExplosionTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"

    private val testClass = "test.samples.BaseOnlySummaryFieldExplosionSample"
    private val ruleId = "baseonly-summary-field-explosion"
    private val mark = "summary-field-explosion-taint"
    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(testClass, "source", mark)),
        sink = listOf(sinkRule(testClass, "sink", ruleId, listOf(Argument(0) to mark))),
    )

    @Test
    fun `field enumeration preserves the trace witness in both ap modes`() {
        val treeVulnerabilities = runAnalysis(
            config = config,
            entryPointClass = testClass,
            entryPointMethod = "fieldEnumerationExplosion",
            apMode = ApMode.Tree,
        )
        assertResolvedHelperTrace(treeVulnerabilities, "Tree")

        val baseOnlyVulnerabilities = runAnalysis(
            config = config,
            entryPointClass = testClass,
            entryPointMethod = "fieldEnumerationExplosion",
            apMode = ApMode.BaseOnlyField,
        )
        assertResolvedHelperTrace(baseOnlyVulnerabilities, "BaseOnly")
    }

    @Test
    fun `irrelevant call retains the exact source-to-sink premises`() {
        val vulnerabilities = runAnalysis(
            config = config,
            entryPointClass = testClass,
            entryPointMethod = "irrelevantCallConclusionSharing",
            apMode = ApMode.BaseOnlyField,
        )

        assertTrue(vulnerabilities.isNotEmpty(), "the exact source-to-sink premises must be retained")
    }

    private fun assertResolvedHelperTrace(
        vulnerabilities: List<VulnerabilityWithTrace>,
        mode: String,
    ) {
        assertTrue(vulnerabilities.isNotEmpty(), "$mode must preserve the source-to-sink flow")
        val paths = vulnerabilities.mapNotNull { it.trace as? TracePathGenerationResult.Path }
        assertTrue(paths.isNotEmpty(), "$mode must resolve a complete trace path")
        assertTrue(
            paths.any { path ->
                path.path.any { node ->
                    (node.root2Source + node.root2SinkNoRoot).any { it.containsMethod("permuteField") }
                }
            },
            "$mode trace must resolve the generalized permuteField summary",
        )
    }

    private fun ResolvedInterProceduralTrace.containsMethod(name: String): Boolean {
        if (method.method.name == name) return true
        return entries.any { entry ->
            entry is ResolvedInterProceduralTraceEntry.InnerCall && entry.innerTrace.containsMethod(name)
        }
    }

}
