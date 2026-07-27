package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.access.baseonly.ABSTRACT_EMPTY_ACCESS
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyFinalFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyInitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.ap.ifds.trace.path.ResolvedInterProceduralTrace
import org.opentaint.dataflow.ap.ifds.trace.path.ResolvedInterProceduralTraceEntry
import org.opentaint.dataflow.ap.ifds.trace.path.TracePathGenerationResult
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.ifds.SingletonUnit

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
    fun `field generalization bounds the summary family and preserves its trace witness`() {
        var helperSummaries = emptyList<Edge.FactToFact>()

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
        ) { analyzer, graph ->
            val cls = cp.findClassOrNull(testClass) ?: error("Class $testClass not found")
            val helper = cls.declaredMethods.single { it.name == "permuteField" }
            val entryStatement = graph.methodGraph(helper).entryPoints().single()
            val entryPoint = MethodEntryPoint(EmptyMethodContext, entryStatement)
            val summaries = analyzer.ifdsEngine.getOrCreateUnitStorage(SingletonUnit)
                ?: error("No summary storage for $helper")

            helperSummaries = summaries.methodFactToFactSummaryEdges(
                entryPoint,
                AccessPathBase.Return,
            )
        }
        assertResolvedHelperTrace(baseOnlyVulnerabilities, "BaseOnly")

        val generalizedTransfers = helperSummaries.mapNotNull { edge ->
            val initial = edge.initialFactAp as? BaseOnlyInitialFactAp ?: return@mapNotNull null
            val final = edge.factAp as? BaseOnlyFinalFactAp ?: return@mapNotNull null
            if (initial.base != AccessPathBase.Argument(0)) return@mapNotNull null
            if (final.base != AccessPathBase.Return) return@mapNotNull null
            edge
        }

        assertEquals(1, generalizedTransfers.size, "the precise summary family must generalize to one edge")
        val generalized = generalizedTransfers.single()
        val initial = generalized.initialFactAp as BaseOnlyInitialFactAp
        val final = generalized.factAp as BaseOnlyFinalFactAp
        assertEquals(ABSTRACT_EMPTY_ACCESS, initial.access)
        assertEquals(ABSTRACT_EMPTY_ACCESS, final.access)
        assertEquals(
            initial.exclusions,
            final.exclusions,
            "the generalized edge must carry one correlated suffix-exclusion union",
        )
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
