package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.access.baseonly.ABSTRACT_MARK
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyFinalFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyInitialFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.NO_ACCESSOR
import org.opentaint.dataflow.ap.ifds.access.baseonly.fieldIdx
import org.opentaint.dataflow.ap.ifds.access.baseonly.staticIdx
import org.opentaint.dataflow.ap.ifds.access.baseonly.suffixIdx
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
    fun `nondeterministic field permutation produces a massive summary family`() {
        var helperSummaries = emptyList<Edge.FactToFact>()

        val vulnerabilities = runAnalysis(
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
                AccessPathBase.Argument(0),
            )
        }

        assertTrue(vulnerabilities.isNotEmpty(), "the field permutation must preserve a source-to-sink flow")

        val fieldTransfers = helperSummaries.mapNotNull { edge ->
            val initial = edge.initialFactAp as? BaseOnlyInitialFactAp ?: return@mapNotNull null
            val final = edge.factAp as? BaseOnlyFinalFactAp ?: return@mapNotNull null
            if (initial.base != AccessPathBase.Argument(0)) return@mapNotNull null
            if (initial.access.staticIdx != NO_ACCESSOR || final.access.staticIdx != NO_ACCESSOR) {
                return@mapNotNull null
            }
            if (initial.access.fieldIdx < 0 || final.access.fieldIdx < 0) return@mapNotNull null
            if (initial.access.suffixIdx != ABSTRACT_MARK || final.access.suffixIdx != ABSTRACT_MARK) {
                return@mapNotNull null
            }
            initial.access.fieldIdx to final.access.fieldIdx
        }.toSet()
        val fieldAbstractIdentityEdges = helperSummaries.count { edge ->
            val initial = edge.initialFactAp as? BaseOnlyInitialFactAp ?: return@count false
            val final = edge.factAp as? BaseOnlyFinalFactAp ?: return@count false
            initial.base == AccessPathBase.Argument(0) &&
                initial.access.staticIdx == NO_ACCESSOR &&
                initial.access.fieldIdx == ABSTRACT_MARK &&
                initial.access.suffixIdx == NO_ACCESSOR &&
                final.access.staticIdx == NO_ACCESSOR &&
                final.access.fieldIdx == ABSTRACT_MARK &&
                final.access.suffixIdx == NO_ACCESSOR
        }
        val fieldErasureEdges = helperSummaries.count { edge ->
            val initial = edge.initialFactAp as? BaseOnlyInitialFactAp ?: return@count false
            val final = edge.factAp as? BaseOnlyFinalFactAp ?: return@count false
            initial.base == AccessPathBase.Argument(0) &&
                initial.access.staticIdx == NO_ACCESSOR &&
                initial.access.fieldIdx >= 0 &&
                initial.access.suffixIdx == ABSTRACT_MARK &&
                final.access.staticIdx == NO_ACCESSOR &&
                final.access.fieldIdx == NO_ACCESSOR &&
                final.access.suffixIdx == ABSTRACT_MARK
        }

        assertTrue(fieldTransfers.isEmpty(), "abstract conclusions subsume all concrete-field relocations")
        assertEquals(20, fieldErasureEdges, "every selected field also flows to the abstract object tail")
        assertEquals(1, fieldAbstractIdentityEdges, "the object identity is stored as (-1, -2, -1) -> itself")
        assertEquals(1 + 20, helperSummaries.size, "conclusion subsumption reduces 401 edges to 21")
    }
}
