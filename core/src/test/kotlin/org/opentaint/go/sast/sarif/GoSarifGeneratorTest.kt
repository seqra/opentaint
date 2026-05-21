package org.opentaint.go.sast.sarif

import io.github.detekt.sarif4k.Result
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.go.sast.dataflow.AnalysisTest
import org.opentaint.go.sast.dataflow.GoStubRules
import org.opentaint.go.sast.dataflow.GoTaintAnalyzer
import org.opentaint.go.sast.dataflow.GoUnitResolver
import org.opentaint.ir.go.ext.findFunctionByFullName
import org.opentaint.jvm.sast.project.SarifGenerationOptions
import kotlin.test.assertNotNull

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GoSarifGeneratorTest : AnalysisTest() {

    private fun analyzeWithFacade(entryPointFn: String): List<VulnerabilityWithTrace> {
        val entryPoint = cp.findFunctionByFullName(entryPointFn)
            ?: error("Entry point not found: $entryPointFn")
        val analyzer = GoTaintAnalyzer(
            cp = cp,
            taintConfig = GoStubRules.defaultConfig(),
            unitResolver = GoUnitResolver(setOf("test")),
        )
        return analyzer.analyzeWithIfds(listOf(entryPoint))
    }

    @Test
    fun `generates sarif with sink location and code flow`() {
        val traces = analyzeWithFacade("test.noKill001T")
        assertTrue(traces.isNotEmpty(), "Expected at least one source-to-sink trace")

        val generator = GoSarifGenerator(SarifGenerationOptions(), sourcesDir)
        val report = generator.generateSarif(traces.asSequence())

        val results: List<Result> = report.runs.flatMap { it.results.toList() }
        println("Go SARIF results: ${results.size}")
        assertTrue(results.isNotEmpty(), "Expected at least one SARIF result")

        assertTrue(results.size == 1, "Expected exactly one SARIF result, got ${results.size}")
        val result = results.first()
        assertTrue(
            result.ruleID == GoStubRules.SINK_RULE_ID,
            "Unexpected rule id: ${result.ruleID}",
        )

        // Sink physical location resolved from GoIRPosition.
        val sinkPhysical = assertNotNull(
            result.locations?.firstOrNull()?.physicalLocation,
            "Expected sink physical location",
        )
        val sinkRegion = assertNotNull(sinkPhysical.region, "Expected sink region")
        assertTrue((sinkRegion.startLine ?: 0L) > 0L, "Expected positive sink start line")
        val sinkUri = assertNotNull(sinkPhysical.artifactLocation?.uri, "Expected sink uri")
        assertTrue(sinkUri.endsWith(".go"), "Expected a Go source uri, got: $sinkUri")

        // Code flow with meaningful messages.
        val flowLocations = results
            .flatMap { it.codeFlows.orEmpty() }
            .flatMap { it.threadFlows }
            .flatMap { it.locations }
        println("Go flow messages: " + flowLocations.mapNotNull { it.location?.message?.text })
        assertTrue(flowLocations.isNotEmpty(), "Expected code-flow locations")

        val messages = flowLocations.mapNotNull { it.location?.message?.text }
        assertTrue(
            messages.any { it.startsWith("Tainted") },
            "Expected a source message in the flow, got: $messages",
        )
        assertTrue(
            messages.any { it == GoStubRules.defaultSinks.first().meta.message },
            "Expected the sink message in the flow, got: $messages",
        )

        // Every flow location resolved to a Go source position.
        flowLocations.forEach { tfl ->
            val region = assertNotNull(tfl.location?.physicalLocation?.region, "Flow location missing region")
            assertTrue((region.startLine ?: 0L) > 0L, "Flow location with non-positive line")
        }
    }
}
