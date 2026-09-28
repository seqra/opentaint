package org.opentaint.jvm.sast.dataflow.backward

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
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
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class BackwardForwardDifferentialTest : BackwardAnalysisTest() {
    data class Divergence(
        val caseId: String,
        val ruleId: String,
        val reason: String,
        val modes: Set<ApMode>,
        val backwardReaches: Boolean,
    )

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

        private const val STAR_FACT_EXACT_CLEANER =
            "forward holds the any-field entry fact as the star path x.[any].M when the Exact cleaner on x runs in the same method and " +
                "Cleaner.kt removes the whole star; backward demands the concrete path x.k.M, which the cleaner keeps"

        private const val FORWARD_KNOWN_FALSE_NEGATIVE =
            "the forward suite disables this flow as a known false negative (List<List<T>>); the nested element is representable here " +
                "and backward reports the real flow, while forward drops the vulnerability its IFDS facts reach"

        private val ALL_MODES = ApMode.entries.toSet()
        private val TREE = setOf(ApMode.Tree)
        private val AUTOMATA = setOf(ApMode.Automata)

        private fun divergence(suite: String, case: String, rule: String, reason: String, modes: Set<ApMode>, backwardReaches: Boolean) =
            Divergence("$suite/$case", rule, reason, modes, backwardReaches)

        val commonDivergences: List<Divergence> = buildList {
            val java = ForwardSuiteCases.JAVA_REACHABILITY
            val dual = ForwardSuiteCases.CLEANER_STAR_DUAL

            add(divergence(java, "lambdaCaptureFlow", "reach", LAMBDA_RESOLUTION, ALL_MODES, false))
            add(divergence(java, "streamFlatMapFlow", "reach", FORWARD_KNOWN_FALSE_NEGATIVE, AUTOMATA, true))
            add(divergence(dual, "inlineCleanerThenFieldSink", "field-sink", STAR_FACT_EXACT_CLEANER, TREE, true))
        }
    }

    open val checkForwardExpectations: Boolean = false

    open val acceptSuiteExpectation: Boolean = true

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

    private fun forwardIsolatedRuleIds(case: ForwardCase, group: SinkGroup): Set<String> = withCase(case) {
        group.sinks.flatMapTo(hashSetOf()) { sink ->
            runAnalysis(case.config.copy(sink = listOf(sink)), case.entryClass, case.entryMethod)
                .map { it.vulnerability.rule.id }
        }
    }

    private fun backwardMarks(case: ForwardCase, group: SinkGroup): Set<String> = withCase(case) {
        val result = runBackwardAnalysis(case.config.copy(sink = group.sinks), case.entryClass, case.entryMethod)
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status, "${case.id}: backward analysis status")
        result.sourceFindings.mapTo(hashSetOf()) { it.mark.mark }
    }

    @TestFactory
    fun `backward agrees with forward`(): List<DynamicNode> {
        val divergenceIndex = divergences.filter { apMode in it.modes }.associateBy { it.caseId to it.ruleId }
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
        val groupRules = group.marksByRule.keys
        val suite = case.expectedRuleIds.intersect(groupRules)
        if (checkForwardExpectations) {
            assertEquals(
                suite,
                forwardRuleIds(case).intersect(groupRules),
                "${case.id}: forward result differs from the forward suite expectation",
            )
        }

        val forward = forwardIsolatedRuleIds(case, group)
        val backward = backwardMarks(case, group)

        val mismatches = mutableListOf<String>()
        for ((ruleId, marks) in group.marksByRule) {
            val backwardReached = backward.containsAll(marks)
            val forwardReached = ruleId in forward
            val suiteExpects = ruleId in suite
            val divergence = divergenceIndex[case.id to ruleId]

            val agrees = when {
                divergence != null -> backwardReached == divergence.backwardReaches &&
                    backwardReached != forwardReached &&
                    (!acceptSuiteExpectation || backwardReached != suiteExpects)

                acceptSuiteExpectation -> backwardReached == forwardReached || backwardReached == suiteExpects
                else -> backwardReached == forwardReached
            }

            if (!agrees) {
                mismatches += "$ruleId: backward=$backwardReached forward=$forwardReached suite=$suiteExpects divergence=${divergence?.reason}"
            }
        }

        assertTrue(mismatches.isEmpty(), "${case.id} group ${group.index}: ${mismatches.joinToString("; ")}")
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
    override val acceptSuiteExpectation: Boolean = false
}

class AutomataBackwardForwardDifferentialTest : BackwardForwardDifferentialTest() {
    override val apMode: ApMode = ApMode.Automata
}
