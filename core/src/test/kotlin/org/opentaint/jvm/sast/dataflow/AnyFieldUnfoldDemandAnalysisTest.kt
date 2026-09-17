package org.opentaint.jvm.sast.dataflow

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Timeout
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier.AnyField
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.jvm.ap.ifds.JIRSafeApplicationGraph
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.impl.features.usagesExt
import org.opentaint.jvm.graph.JApplicationGraphImpl
import org.opentaint.jvm.sast.dataflow.DataFlowApproximationLoader.isApproximation
import org.opentaint.jvm.sast.dataflow.rules.TaintConfiguration
import org.opentaint.util.analysis.ApplicationGraph
import java.util.concurrent.TimeUnit
import kotlin.time.Duration.Companion.minutes

/**
 * The mark-unfold demand iterating on its own output, at unit scale.
 *
 * `MethodSideEffectHandlerWithAnyAccessorRequestHandling` answers a `TaintMarkFieldUnfoldRequest`
 * by re-posting the asking frame's fact with the mark-bearing accessors excluded. Splitting `a` out
 * of `arg0.[any]` produces `arg0.a.[any]` -- an abstraction that ends in `[any]` again, one
 * accessor deeper, which re-raises the same question. Nothing stops an answer from contributing an
 * accessor that was already demanded for the same (frame, base, mark) question, so on a
 * self-similar shape the demand iterates on its own output, and the request population grows
 * exponentially in the container's branching factor.
 *
 * [test.samples.AnyFieldUnfoldDemandSample] is that shape: a six-way self-similar `Cell` whose
 * fields are closed into a cycle on a loop back edge, carried to the sink through a chain of
 * forwarding frames. The flow is a genuine true positive -- the taint really reaches a field of the
 * sink argument -- so the assertion is about RESULT plus TERMINATION: the analyzer must report the
 * flow AND finish inside its own IFDS budget.
 *
 * ## What the two tests separate
 *
 * Both tests analyse the SAME program with the SAME marks. They differ only in whether the sink
 * condition carries the `AnyField` modifier -- i.e. only in whether the unfold demand is raised at
 * all. The control finishes in well under a second, so the separation is attributable to the demand
 * and to nothing else about the sample.
 *
 * ## Why this size
 *
 * The request population multiplies across three independent axes: chain length (linear), sibling
 * marks (linear), and the container's branching factor (EXPONENTIAL -- which is why the sample uses
 * six self-typed fields rather than one; a single self-field is linear no matter how deep the heap
 * cycle or the call chain goes).
 *
 * Verified on this machine (4 GB test heap, `ifdsTimeout` = 1 minute), by stashing the engine
 * changes and re-running the identical test:
 *
 * | chain | marks | engine                        | result  |
 * |-------|-------|-------------------------------|---------|
 * | 40    | 8     | without the unroll/merge fixes | TIMEOUT |
 * | 40    | 8     | with them                     | PASS    |
 * | 40    | 16    | with them                     | TIMEOUT |
 *
 * So the shipped arm sits one step below a cliff that is still there: the demand is cheaper per
 * request, not smaller. If this needs re-tuning for a faster machine, raise [MARKS] first -- it is
 * the linear axis, so it moves the cost predictably.
 */
class AnyFieldUnfoldDemandAnalysisTest : AnalysisTest() {
    companion object {
        private const val TEST_CLASS = "test.samples.AnyFieldUnfoldDemandSample"
        private const val RULE_ID = "any-field-unfold-demand"

        /** Sibling marks asking one question -- the multiplier the real workload shows as ~8.5x. */
        private const val MARKS = 8

        private const val ENTRY_POINT = "chain40"
    }

    override val sourceFileExtension: String = "java"

    /**
     * Same as `AnyFieldInterproceduralAnalysisTest`: only field accessors are unrolled. The
     * container accessors this shape needs (`Cell#a` .. `Cell#f`) are field accessors, and so are
     * the erased container accessors the real workload stalls on (`Map#MapValue`,
     * `CharSequence#content`), so this strategy covers both.
     */
    override val analysisUnrollStrategy: AnyAccessorUnrollStrategy = object : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = accessor is FieldAccessor
    }

    /**
     * The demand arm. This is the case that is cancelled on `ifdsTimeout` rather than reaching a
     * fixed point when the unroll/merge work is not shared -- see the table above.
     */
    @Test
    @Timeout(value = 2, unit = TimeUnit.MINUTES)
    fun `any-field unfold demand converges on a self-similar container`() {
        val (traces, status) = analyze(config(anyField = true))

        assertTrue(
            traces.isNotEmpty(),
            "expected the taint to reach the sink, but no vulnerability with a trace was found"
        )
        assertEquals(
            TaintAnalysisUnitRunnerManager.Status.OK, status.analysisStatus,
            "the any-field unfold demand did not reach a fixed point: the analysis was cancelled" +
                " with status ${status.analysisStatus}. The control test shows the same program" +
                " analysed with a base-only sink condition finishes in well under a second."
        )
    }

    /**
     * The control: identical program, identical marks, sink condition without `AnyField`, so no
     * unfold request is ever raised. Pins that the sample itself is trivial to analyse and that the
     * cost in the test above belongs to the demand.
     */
    @Test
    @Timeout(value = 2, unit = TimeUnit.MINUTES)
    fun `control - the same program without an any-field condition converges`() {
        val (_, status) = analyze(config(anyField = false))

        assertEquals(
            TaintAnalysisUnitRunnerManager.Status.OK, status.analysisStatus,
            "the control arm is expected to converge"
        )
    }

    private fun config(anyField: Boolean): SerializedTaintConfig {
        val marks = (0 until MARKS).map { "tainted$it" }
        return SerializedTaintConfig(
            source = marks.map { sourceRule(TEST_CLASS, "source", it) },
            sink = marks.mapIndexed { i, mark ->
                SerializedRule.Sink(
                    function = functionMatcher(TEST_CLASS, "sink"),
                    condition = SerializedCondition.ContainsMark(
                        tainted = mark,
                        pos = if (anyField) {
                            PositionBaseWithModifiers.WithModifiers(Argument(0), listOf(AnyField))
                        } else {
                            PositionBaseWithModifiers.BaseOnly(Argument(0))
                        },
                    ),
                    id = "$RULE_ID-$i",
                    meta = SinkMetaData(note = "Taint reaches a field of the sink argument"),
                )
            },
        )
    }

    private class SingleLocationUnit(val loc: RegisteredLocation) : JIRUnitResolver {
        override fun resolve(method: JIRMethod): UnitType =
            if (method.enclosingClass.declaration.location == loc || isApproximation(method)) {
                SingletonUnit
            } else {
                UnknownUnit
            }

        override fun locationIsUnknown(loc: RegisteredLocation): Boolean = loc != this.loc
    }

    /**
     * [AnalysisTest.runAnalysis] drops the engine's completion status, and the status is exactly
     * what this test is about, so the wiring is repeated here to keep it. Everything else matches
     * the base class.
     */
    private fun analyze(
        config: SerializedTaintConfig
    ): Pair<List<VulnerabilityWithTrace>, TaintAnalyzer.Status> {
        val cls = cp.findClassOrNull(TEST_CLASS) ?: error("Class $TEST_CLASS not found in CP")
        val ep = cls.declaredMethods.single { it.name == ENTRY_POINT }

        val taintConfig = TaintConfiguration(cp)
        taintConfig.loadConfig(config)

        var rulesProvider: TaintRulesProvider = JIRTaintRulesProvider(taintConfig)
        rulesProvider = JIRMethodExitRuleProvider(rulesProvider)

        val usages = runBlocking { cp.usagesExt() }
        val ifdsGraph = JIRSafeApplicationGraph(JApplicationGraphImpl(cp, usages))

        val options = TaintAnalyzerOptions(ifdsTimeout = 1.minutes, ifdsApMode = apMode)

        val analyzer = object : TaintAnalyzer<JIRMethod, JIRInst>(options) {
            override val unrollStrategy: AnyAccessorUnrollStrategy
                get() = analysisUnrollStrategy

            override fun analysisGraph(): ApplicationGraph<JIRMethod, JIRInst> = ifdsGraph
            override fun analysisManager() = JIRAnalysisManager(cp, refManager, rulesProvider)
            override fun unitResolver() = SingleLocationUnit(cls.declaration.location)
        }

        return analyzer.use { it.analyzeWithIfds(listOf(ep)) }
    }
}
