package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.ir.go.ext.findFunctionByFullName
import kotlin.test.Test
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class FactReachabilityExportTest : AnalysisTest() {

    @Test fun statementsWithFactsNonEmptyForTaintedSample() {
        val config = GoSerializedTaintConfig(source = listOf(stdSource), sink = listOf(stdSink))
        val loaded = GoTaintConfiguration().apply { loadConfig(config) }
        val entry = cp.findFunctionByFullName("test.sample")!!
        GoTaintAnalyzer(cp, loaded, GoTestUnitResolver).use { analyzer ->
            analyzer.analyzeWithIfds(listOf(entry))
            val facts = analyzer.statementsWithFacts()
            assertTrue(facts.isNotEmpty(), "expected per-statement facts")
            assertTrue(facts.values.any { it.isNotEmpty() }, "expected ≥1 tainted statement")
        }
    }
}
