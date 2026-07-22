package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.FactPropagationTracer
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers.WithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier.Field
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

class SuffixTreePropagationTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"
    override val useDefaultConfig: Boolean = true

    private data class Run(
        val findings: List<String>,
        val events: List<FactPropagationTracer.Event>,
    )

    private data class RelationKey(
        val kind: FactPropagationTracer.Kind,
        val method: String,
        val initialBase: String,
        val finalBase: String,
        val initialFact: String,
        val finalFact: String,
    )

    @Test
    fun `suffix callback propagation covers Tree baseline`() {
        val testClass = "test.samples.AsyncDataFlowSample"
        val config = SerializedTaintConfig(
            source = listOf(sourceRule(testClass, "source", "tainted")),
            sink = listOf(
                sinkRule(testClass, "sink", "async-flow", listOf(Argument(0) to "tainted"))
            ),
        )

        fun run(mode: ApMode): Run {
            FactPropagationTracer.reset()
            FactPropagationTracer.enabled = true
            val findings = try {
                runAnalysis(config, testClass, "threadRunnableFlow", mode)
            } finally {
                FactPropagationTracer.enabled = false
            }
            return Run(
                findings.map { it.vulnerability.rule.id }.sorted(),
                FactPropagationTracer.snapshot(),
            )
        }

        fun skeleton(run: Run) = run.events.flatMap { event ->
            event.materializedFactToFact.map { fact ->
                listOf(
                    event.kind.toString(),
                    event.methodEntryPoint.method.toString(),
                    fact.statement,
                    fact.initialBase,
                    fact.finalBase,
                )
            }
        }.toSet()

        val tree = run(ApMode.Tree)
        val suffix = run(ApMode.SuffixTree)
        val missing = skeleton(tree) - skeleton(suffix)
        assertTrue(missing.isEmpty(), "SuffixTree callback propagation lost Tree edges: $missing")
        assertEquals(tree.findings, suffix.findings, "SuffixTree callback findings diverged from Tree")
        assertTrue(tree.findings.isNotEmpty(), "callback fixture did not reach the sink in Tree mode")
    }

    @Test
    fun `suffix propagation retains factored trees and covers Tree baseline`() {
        val testClass = "test.samples.SuffixTreePropagationSample"
        val pairClass = "$testClass\$Pair"
        val config = SerializedTaintConfig(
            entryPoint = listOf(
                SerializedRule.EntryPoint(
                    function = functionMatcher(testClass, "commonBaseIdentityEntry"),
                    taint = listOf("left", "right").map { field ->
                        SerializedTaintAssignAction(
                            kind = "tainted",
                            pos = WithModifiers(
                                Argument(0),
                                listOf(Field(pairClass, field, "java.lang.String")),
                            ),
                        )
                    },
                )
            ),
            sink = listOf(
                sinkRule(
                    testClass,
                    "sink",
                    "suffix-propagation",
                    listOf(Argument(0) to "tainted"),
                )
            ),
        )

        fun run(mode: ApMode): Run {
            FactPropagationTracer.reset()
            FactPropagationTracer.enabled = true
            val findings = try {
                runAnalysis(config, testClass, "commonBaseIdentityEntry", mode)
            } finally {
                FactPropagationTracer.enabled = false
            }
            return Run(
                findings.map { it.vulnerability.rule.id }.sorted(),
                FactPropagationTracer.snapshot(),
            )
        }

        val tree = run(ApMode.Tree)
        val suffix = run(ApMode.SuffixTree)
        assertEquals(listOf("suffix-propagation", "suffix-propagation"), tree.findings)
        assertEquals(tree.findings, suffix.findings, "SuffixTree findings diverged from Tree")

        fun propagationSkeleton(run: Run) = run.events.flatMap { event ->
            event.materializedFactToFact.map { materialized ->
                listOf(
                    event.kind.toString(),
                    event.methodEntryPoint.method.toString(),
                    materialized.statement,
                    materialized.initialBase,
                    materialized.finalBase,
                )
            }
        }.toSet()

        val missingFromSuffix = propagationSkeleton(tree) - propagationSkeleton(suffix)
        assertTrue(
            missingFromSuffix.isEmpty(),
            "SuffixTree propagation lost Tree statement/base transitions: $missingFromSuffix",
        )

        val suffixFactEvents = suffix.events.mapNotNull { event ->
            (event.edge as? Edge.FactToFact)?.let { event to it }
        }
        val nonEmptyEvents = suffixFactEvents.filter { (_, edge) ->
            edge.suffixBundle?.suffixTree?.hasNonEmptySuffix() == true
        }
        assertTrue(nonEmptyEvents.isNotEmpty(), "fixture did not exercise a non-empty suffix tree")
        nonEmptyEvents.forEach { (event, edge) ->
            assertTrue(event.materializedFactToFact.isNotEmpty(), "non-empty suffix materialized to no facts")
            assertNotNull(edge.suffixBundle)
        }

        fun FactPropagationTracer.Event.keys(): List<RelationKey> =
            materializedFactToFact.map {
                RelationKey(
                    kind,
                    methodEntryPoint.method.toString(),
                    it.initialBase,
                    it.finalBase,
                    it.initialFact,
                    it.finalFact,
                )
            }

        val factoredAt = buildMap<RelationKey, Long> {
            for ((event, edge) in nonEmptyEvents) {
                if (edge.suffixBundle?.isIdentityForSameBase() != true) continue
                event.keys().forEach { putIfAbsent(it, event.sequence) }
            }
        }
        assertTrue(factoredAt.isNotEmpty(), "fixture did not propagate a factored identity relation")

        var checkedContinuation = false
        for ((event, edge) in suffixFactEvents) {
            for (key in event.keys()) {
                val firstFactored = factoredAt[key] ?: continue
                if (event.sequence <= firstFactored) continue
                checkedContinuation = true
                val bundle = edge.suffixBundle
                assertTrue(
                    bundle != null && bundle.suffixTree.hasNonEmptySuffix(),
                    "factored relation degenerated at #${event.sequence} ${edge.statement} " +
                        "in ${event.methodEntryPoint}: $key, bundle=${edge.suffixBundle}",
                )
            }
        }
        assertTrue(checkedContinuation, "fixture did not carry a factored identity beyond its first edge")
    }
}
