package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.MethodStats
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class ThingsBoardEntityActionExplosionTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"

    private val testClass = "test.samples.ThingsBoardEntityActionExplosionSample"
    private val ruleId = "thingsboard-entity-action-explosion"
    private val mark = "thingsboard-entity-action-taint"
    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(testClass, "source", mark)),
        sink = listOf(sinkRule(testClass, "sink", ruleId, listOf(Argument(0) to mark))),
    )

    private val safeContextRuleId = "thingsboard-context-support-safe"
    private val taintedContextRuleId = "thingsboard-context-support-tainted"
    private val contextSupportConfig = SerializedTaintConfig(
        source = listOf(sourceRule(testClass, "source", mark)),
        sink = listOf(
            sinkRule(testClass, "safeContextSink", safeContextRuleId, listOf(Argument(0) to mark)),
            sinkRule(testClass, "taintedContextSink", taintedContextRuleId, listOf(Argument(0) to mark)),
        ),
    )

    @Test
    fun `interface contexts multiply the branch-heavy entity action analysis`() {
        val single = analyzePushWorkload("singleEntityAction")
        val contextual = analyzePushWorkload("entityActionExplosion")

        assertTrue(
            contextual.steps >= single.steps * 4,
            "six concrete interface contexts must multiply analysis steps: single=$single, contextual=$contextual",
        )
        assertTrue(
            contextual.handledSummaries >= single.handledSummaries * 4,
            "six concrete interface contexts must multiply summary applications: single=$single, contextual=$contextual",
        )
        println("ThingsBoard entity-action reproduction: single=$single, contextual=$contextual")
    }

    @Test
    fun `context support batching preserves exact method contexts`() {
        for (mode in listOf(ApMode.Tree, ApMode.BaseOnlyField)) {
            val ruleIds = runAnalysis(
                config = contextSupportConfig,
                entryPointClass = testClass,
                entryPointMethod = "contextSupportedSideEffectBatch",
                apMode = mode,
            ).mapTo(mutableSetOf()) { it.vulnerability.rule.id }

            assertEquals(
                setOf(taintedContextRuleId),
                ruleIds,
                "$mode must not attach the tainted local transfer to the unsupported SafeContext",
            )
        }
    }

    @Test
    fun `identical fact propagation is multiplied by its exact context support`() {
        val single = analyzeContextWorkload("singleContextSupportedSideEffect")
        val contextual = analyzeContextWorkload("contextSupportedSideEffectBatch")

        assertTrue(
            contextual.steps >= single.steps * 4,
            "seven contexts carrying the same fact must expose duplicated local work: " +
                "single=$single, contextual=$contextual",
        )
        assertTrue(
            contextual.handledSummaries >= single.handledSummaries * 4,
            "seven contexts carrying the same fact must expose duplicated summary work: " +
                "single=$single, contextual=$contextual",
        )
        println("ThingsBoard exact-context support: single=$single, contextual=$contextual")
    }

    @Test
    fun `BaseOnly bypasses control-only statements without losing the exact edge`() {
        val tree = analyzeMethod("controlOnlyFanout", ApMode.Tree)
        val baseOnly = analyzeMethod("controlOnlyFanout", ApMode.BaseOnlyField)

        assertTrue(
            baseOnly.steps < tree.steps,
            "BaseOnly should not tabulate an unchanged fact at every control-only statement: " +
                "tree=$tree, baseOnly=$baseOnly",
        )
    }

    private fun analyzePushWorkload(entryPoint: String): MethodStats.Stats {
        var pushStats: MethodStats.Stats? = null
        val vulnerabilities = runAnalysis(
            config = config,
            entryPointClass = testClass,
            entryPointMethod = entryPoint,
            apMode = ApMode.BaseOnlyField,
        ) { analyzer, _ ->
            val pushMethod = cp.findClassOrNull(testClass)!!.declaredMethods
                .single { it.name == "pushEntityActionToRuleEngine" }
            pushStats = analyzer.ifdsEngine.collectMethodStats().stats[pushMethod]
        }
        assertTrue(vulnerabilities.isNotEmpty(), "$entryPoint must preserve source-to-sink flow")
        return requireNotNull(pushStats)
    }

    private fun analyzeContextWorkload(entryPoint: String): MethodStats.Stats {
        var processStats: MethodStats.Stats? = null
        val ruleIds = runAnalysis(
            config = contextSupportConfig,
            entryPointClass = testClass,
            entryPointMethod = entryPoint,
            apMode = ApMode.BaseOnlyField,
        ) { analyzer, _ ->
            val processMethod = cp.findClassOrNull(testClass)!!.declaredMethods
                .single { it.name == "processContext" }
            processStats = analyzer.ifdsEngine.collectMethodStats().stats[processMethod]
        }.mapTo(mutableSetOf()) { it.vulnerability.rule.id }

        assertEquals(
            setOf(taintedContextRuleId),
            ruleIds,
            "$entryPoint must retain the exact context-to-sink association",
        )
        return requireNotNull(processStats)
    }

    private fun analyzeMethod(entryPoint: String, mode: ApMode): MethodStats.Stats {
        var methodStats: MethodStats.Stats? = null
        val vulnerabilities = runAnalysis(
            config = config,
            entryPointClass = testClass,
            entryPointMethod = entryPoint,
            apMode = mode,
        ) { analyzer, _ ->
            val method = cp.findClassOrNull(testClass)!!.declaredMethods
                .single { it.name == entryPoint }
            methodStats = analyzer.ifdsEngine.collectMethodStats().stats[method]
        }
        assertTrue(vulnerabilities.isNotEmpty(), "$mode must preserve source-to-sink flow")
        return requireNotNull(methodStats)
    }
}
