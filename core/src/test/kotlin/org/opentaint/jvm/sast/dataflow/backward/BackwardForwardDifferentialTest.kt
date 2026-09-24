package org.opentaint.jvm.sast.dataflow.backward

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DynamicContainer
import org.junit.jupiter.api.DynamicNode
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class BackwardForwardDifferentialTest : BackwardAnalysisTest() {
    data class Divergence(val caseId: String, val ruleId: String, val reason: String)

    data class SinkGroup(val index: Int, val sinks: List<SerializedRule.Sink>) {
        val marksByRule: Map<String, Set<String>> = sinks.associate { sink ->
            val ruleId = sink.id ?: error("sink without id")
            ruleId to ForwardSuiteCases.sinkMarks(sink)
        }
    }

    override val sourceFileExtension: String = "java"

    open val divergences: List<Divergence> = commonDivergences

    companion object {
        private const val LAMBDA_RESOLUTION =
            "lambda call resolution needs forward type-info facts; the lambda body holding the sink is never analysed backward, so no demand is seeded"

        private const val STAR_DEMAND_EXACT_CLEANER =
            "the any-field sink is demanded as the star path x.[any].M; an Exact cleaner on x removes the whole star in Cleaner.kt, " +
                "while forward holds the mark on concrete paths x.f...M that the same cleaner keeps"

        private const val STAR_FACT_EXACT_CLEANER =
            "forward holds the any-field entry fact as the star path x.[any].M when the Exact cleaner on x runs in the same method and " +
                "Cleaner.kt removes the whole star; backward demands the concrete path x.k.M, which the cleaner keeps"

        val commonDivergences: List<Divergence> =
            listOf(Divergence("${ForwardSuiteCases.JAVA_REACHABILITY}/lambdaCaptureFlow", "reach", LAMBDA_RESOLUTION)) +
                (1..5).flatMap { markCount ->
                    (1..markCount).map { mark ->
                        Divergence(
                            "${ForwardSuiteCases.CLEANER_DSL}/matrix-$markCount-AnyField",
                            "cleaner-dsl-matrix-AnyField-Plain-AnyField-field-depth0-mark$mark",
                            STAR_DEMAND_EXACT_CLEANER,
                        )
                    }
                } +
                listOf(
                    Divergence("${ForwardSuiteCases.CLEANER_DSL}/field-store", "field-store-any", STAR_DEMAND_EXACT_CLEANER),
                    Divergence("${ForwardSuiteCases.CLEANER_CONTROL_FLOW}/sequentialMarks", "sequenceNestedAfterPlainSink-m1", STAR_DEMAND_EXACT_CLEANER),
                    Divergence("${ForwardSuiteCases.CLEANER_STAR_DUAL}/nestedStoreThenCleanerThenAnySink", "any-sink", STAR_DEMAND_EXACT_CLEANER),
                    Divergence("${ForwardSuiteCases.CLEANER_STAR_DUAL}/inlineCleanerThenFieldSink", "field-sink", STAR_FACT_EXACT_CLEANER),
                )
    }

    open val checkForwardExpectations: Boolean = false

    private var currentCase: ForwardCase? = null

    override val useDefaultConfig: Boolean
        get() = currentCase?.useDefaultConfig ?: false

    override val analysisUnrollStrategy: AnyAccessorUnrollStrategy
        get() = if (currentCase?.unrollFieldsAndElements == true) UnrollFieldsAndElements else AnyAccessorUnrollStrategy.AnyAccessorDisabled

    private val forwardResults = hashMapOf<String, Set<String>>()

    private fun <T> withCase(case: ForwardCase, body: () -> T): T {
        currentCase = case
        try {
            return body()
        } finally {
            currentCase = null
        }
    }

    private fun forwardRuleIds(case: ForwardCase): Set<String> = forwardResults.getOrPut(case.id) {
        withCase(case) {
            runAnalysis(case.config, case.entryClass, case.entryMethod)
                .mapTo(hashSetOf()) { it.vulnerability.rule.id }
        }
    }

    private fun backwardMarks(case: ForwardCase, group: SinkGroup): Set<String> = withCase(case) {
        val result = runBackwardAnalysis(case.config.copy(sink = group.sinks), case.entryClass, case.entryMethod)
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status, "${case.id}: backward analysis status")
        result.sourceFindings.mapTo(hashSetOf()) { it.mark.mark }
    }

    @TestFactory
    fun `backward agrees with forward`(): List<DynamicNode> {
        val divergenceIndex = divergences.associateBy { it.caseId to it.ruleId }
        return ForwardSuiteCases.all.groupBy { it.suite }.map { (suite, cases) ->
            DynamicContainer.dynamicContainer(suite, cases.map { case ->
                DynamicContainer.dynamicContainer(case.name, sinkGroups(case).map { group ->
                    DynamicTest.dynamicTest("group ${group.index}: ${group.marksByRule.keys.joinToString()}") {
                        checkGroup(case, group, divergenceIndex)
                    }
                })
            })
        }
    }

    private fun checkGroup(case: ForwardCase, group: SinkGroup, divergenceIndex: Map<Pair<String, String>, Divergence>) {
        val forward = forwardRuleIds(case)
        if (checkForwardExpectations) {
            val groupRules = group.marksByRule.keys
            assertEquals(
                case.expectedRuleIds.intersect(groupRules),
                forward.intersect(groupRules),
                "${case.id}: forward result differs from the forward suite expectation",
            )
        }

        val backward = backwardMarks(case, group)
        val expectedMarks = hashSetOf<String>()
        val divergent = mutableListOf<Divergence>()
        for ((ruleId, marks) in group.marksByRule) {
            val forwardReached = ruleId in forward
            val divergence = divergenceIndex[case.id to ruleId]
            if (divergence != null) divergent += divergence
            val backwardExpected = if (divergence != null) !forwardReached else forwardReached
            if (backwardExpected) expectedMarks += marks
        }

        val demanded = group.marksByRule.values.flatten().toSet()
        assertEquals(
            expectedMarks,
            backward.intersect(demanded),
            buildString {
                append("${case.id} group ${group.index}: forward reached ${forward.intersect(group.marksByRule.keys)}")
                if (divergent.isNotEmpty()) append(", accepted divergences $divergent")
            },
        )
    }

    private fun sinkGroups(case: ForwardCase): List<SinkGroup> {
        val groups = mutableListOf<Pair<MutableSet<String>, MutableList<SerializedRule.Sink>>>()
        for (sink in case.sinks) {
            val marks = ForwardSuiteCases.sinkMarks(sink)
            val group = groups.firstOrNull { (groupMarks, _) -> groupMarks.none { it in marks } }
                ?: (hashSetOf<String>() to mutableListOf<SerializedRule.Sink>()).also { groups += it }
            group.first += marks
            group.second += sink
        }
        return groups.mapIndexed { index, (_, sinks) -> SinkGroup(index, sinks) }
    }

    private object UnrollFieldsAndElements : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }
}

class TreeBackwardForwardDifferentialTest : BackwardForwardDifferentialTest() {
    override val checkForwardExpectations: Boolean = true
}
