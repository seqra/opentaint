package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.SummaryTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.FullStart2FinalTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEdge
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.ap.ifds.trace.withMethodRunner
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.ir.api.common.cfg.CommonInst

class TracePremiseCartesianTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"

    private val testClass = "test.samples.TracePremiseCartesianSample"
    private val mark = "trace-premise-cartesian"
    private val oneClauseConfig = SerializedTaintConfig(
        entryPoint = (0..1).map { entryPointRule(testClass, "entryOne", mark, it) },
        sink = listOf(sinkRule(testClass, "sink", "trace-premise-cartesian", listOf(Argument(0) to mark))),
    )
    private val twoClauseConfig = SerializedTaintConfig(
        entryPoint = (0..3).map { entryPointRule(testClass, "entry", mark, it) },
        sink = listOf(sinkRule(testClass, "sink", "trace-premise-cartesian", listOf(Argument(0) to mark))),
    )

    private val threeClauseConfig = SerializedTaintConfig(
        entryPoint = (0..5).map { entryPointRule(testClass, "entryThree", mark, it) },
        sink = listOf(sinkRule(testClass, "sink", "trace-premise-cartesian", listOf(Argument(0) to mark))),
    )

    @Test
    fun `one requested final keeps all origins in one grouped caller summary`() {
        val tree = resolveCallerSummaries(
            mode = ApMode.Tree,
            config = oneClauseConfig,
            entryMethod = "entryOne",
            callerMethod = "multipleOriginsOne",
            calleeMethod = "consumeOne",
            calleeArgumentCount = 1,
        )
        val baseOnly = resolveCallerSummaries(
            mode = ApMode.BaseOnlyField,
            config = oneClauseConfig,
            entryMethod = "entryOne",
            callerMethod = "multipleOriginsOne",
            calleeMethod = "consumeOne",
            calleeArgumentCount = 1,
        )

        assertCartesianFormula(
            tree,
            "Tree",
            requestedFinalCount = 1,
            alternativesPerFinal = 2,
            traceCount = 2,
        )
        assertGroupedFormula(baseOnly, "BaseOnly", requestedFinalCount = 1, alternativesPerFinal = 4)
    }

    @Test
    fun `two requested finals keep alternatives in one grouped caller summary`() {
        val tree = resolveCallerSummaries(
            mode = ApMode.Tree,
            config = twoClauseConfig,
            entryMethod = "entry",
            callerMethod = "multipleOrigins",
            calleeMethod = "consume",
            calleeArgumentCount = 2,
        )
        val baseOnly = resolveCallerSummaries(
            mode = ApMode.BaseOnlyField,
            config = twoClauseConfig,
            entryMethod = "entry",
            callerMethod = "multipleOrigins",
            calleeMethod = "consume",
            calleeArgumentCount = 2,
        )

        assertCartesianFormula(tree, "Tree", alternativesPerFinal = 2, traceCount = 4)
        assertGroupedFormula(baseOnly, "BaseOnly", alternativesPerFinal = 4)

        val baseOnlyAlternatives = baseOnly
            .flatMap { it.final.edges }
            .toSet()
            .groupBy(TraceEdge::fact)
            .values
        for (alternatives in baseOnlyAlternatives) {
            val byOriginBase = alternatives.groupBy { edge ->
                (edge as TraceEdge.MethodTraceEdge).initialFact.base
            }
            assertEquals(2, byOriginBase.size)
            assertTrue(byOriginBase.values.all { it.size == 2 })
            assertTrue(byOriginBase.values.all { sameOrigin ->
                sameOrigin.count { edge ->
                    (edge as TraceEdge.MethodTraceEdge).initialFact.isAbstract()
                } == 1
            })
            assertTrue(byOriginBase.values.all { sameOrigin ->
                sameOrigin.count { edge ->
                    TaintMarkAccessor(mark) in
                        (edge as TraceEdge.MethodTraceEdge).initialFact.getAllAccessors()
                } == 1
            })
        }
    }

    @Test
    fun `three MethodEntry clauses stay grouped instead of materializing a cubic product`() {
        val tree = resolveCallerSummaries(
            mode = ApMode.Tree,
            config = threeClauseConfig,
            entryMethod = "entryThree",
            callerMethod = "multipleOriginsThree",
            calleeMethod = "consumeThree",
            calleeArgumentCount = 3,
        )
        val baseOnly = resolveCallerSummaries(
            mode = ApMode.BaseOnlyField,
            config = threeClauseConfig,
            entryMethod = "entryThree",
            callerMethod = "multipleOriginsThree",
            calleeMethod = "consumeThree",
            calleeArgumentCount = 3,
        )

        assertCartesianFormula(
            tree,
            "Tree",
            requestedFinalCount = 3,
            alternativesPerFinal = 2,
            traceCount = 8,
        )
        assertGroupedFormula(
            baseOnly,
            "BaseOnly",
            requestedFinalCount = 3,
            alternativesPerFinal = 4,
        )
    }

    @Test
    fun `action limit fallback resolves every grouped cube through all trace APIs`() {
        var fallbackVerified = false
        resolveCallerSummaries(
            mode = ApMode.BaseOnlyField,
            config = twoClauseConfig,
            entryMethod = "entry",
            callerMethod = "multipleOrigins",
            calleeMethod = "consume",
            calleeArgumentCount = 2,
        ) { defaultResolver, limitedResolver, summaries ->
            val summary = summaries.single()
            val cancellation = Cancellation()

            val expectedStarts = defaultResolver.resolveIntraProceduralStart2FinalTrace(summary, cancellation)
            val fallbackStarts = limitedResolver.resolveIntraProceduralStart2FinalTrace(summary, cancellation)
            assertEquals(
                expectedStarts.mapTo(hashSetOf()) { it.startEntry },
                fallbackStarts.mapTo(hashSetOf()) { it.startEntry },
            )

            val expectedFull = defaultResolver.resolveIntraProceduralFullStart2FinalTrace(
                summary,
                cancellation,
                collapseUnchangedNodes = false,
            )
            val fallbackFull = limitedResolver.resolveIntraProceduralFullStart2FinalTrace(
                summary,
                cancellation,
                collapseUnchangedNodes = false,
            )
            assertEquals(
                fullTraceEvidence(expectedFull),
                fullTraceEvidence(fallbackFull),
            )

            val groupedStart = expectedStarts.first()
            val expectedFullFromStart = defaultResolver.resolveIntraProceduralFullStart2FinalTrace(
                groupedStart,
                cancellation,
                collapseUnchangedNodes = false,
            )
            val fallbackFullFromStart = limitedResolver.resolveIntraProceduralFullStart2FinalTrace(
                groupedStart,
                cancellation,
                collapseUnchangedNodes = false,
            )
            assertEquals(
                fullTraceEvidence(expectedFullFromStart),
                fullTraceEvidence(fallbackFullFromStart),
            )
            fallbackVerified = true
        }
        assertTrue(fallbackVerified)
    }

    private fun resolveCallerSummaries(
        mode: ApMode,
        config: SerializedTaintConfig,
        entryMethod: String,
        callerMethod: String,
        calleeMethod: String,
        calleeArgumentCount: Int,
        inspect: ((MethodTraceResolver, MethodTraceResolver, List<SummaryTrace>) -> Unit)? = null,
    ): List<SummaryTrace> {
        var result = emptyList<SummaryTrace>()
        val vulnerabilities = runAnalysis(
            config = config,
            entryPointClass = testClass,
            entryPointMethod = entryMethod,
            apMode = mode,
        ) { analyzer, graph ->
            val cls = cp.findClassOrNull(testClass) ?: error("Missing $testClass")
            val caller = cls.declaredMethods.single { it.name == callerMethod }
            val callee = cls.declaredMethods.single { it.name == calleeMethod }
            val callerEntry = MethodEntryPoint(
                EmptyMethodContext,
                graph.methodGraph(caller).entryPoints().single(),
            )
            val calleeEntry = MethodEntryPoint(
                EmptyMethodContext,
                graph.methodGraph(callee).entryPoints().single(),
            )
            val call = caller.flowGraph().instructions.single {
                it.toString().contains(calleeMethod)
            }
            val summaries = analyzer.ifdsEngine.getOrCreateUnitStorage(SingletonUnit)
                ?: error("No summary storage")
            val calleeInitials = (0 until calleeArgumentCount).map { argument ->
                summaries.methodFactToFactSummaryEdges(calleeEntry, AccessPathBase.Argument(argument))
                    .map { it.initialFactAp }
                    .single { initial ->
                        initial.base == AccessPathBase.Argument(argument) &&
                            initial.getAllAccessors().contains(TaintMarkAccessor(mark))
                    }
            }.toSet()

            analyzer.ifdsEngine.withMethodRunner(callerEntry) {
                val defaultResolver = methodTraceResolver(callerEntry)
                result = defaultResolver.resolveIntraProceduralTraceFromCall(
                    call,
                    TraceEntry.MethodEntry(calleeInitials, calleeEntry),
                )
                inspect?.invoke(
                    defaultResolver,
                    methodTraceResolver(callerEntry, traceResolutionActionHardLimit = 0),
                    result,
                )
            }
        }
        assertTrue(vulnerabilities.isNotEmpty(), "$mode must preserve the source-to-sink flow")
        return result
    }

    private fun assertGroupedFormula(
        traces: List<SummaryTrace>,
        mode: String,
        requestedFinalCount: Int = 2,
        alternativesPerFinal: Int,
    ) {
        assertEquals(1, traces.size, "$mode must keep the premise formula grouped")
        assertEquals(
            requestedFinalCount * alternativesPerFinal,
            traces.single().final.edges.size,
            "$mode grouped formula must retain every alternative",
        )

        val alternativesByFinal = traces
            .flatMap { it.final.edges }
            .groupBy(TraceEdge::fact)
            .mapValues { (_, edges) -> edges.toSet() }
        assertEquals(requestedFinalCount, alternativesByFinal.size)
        assertTrue(alternativesByFinal.values.all { it.size == alternativesPerFinal })
    }

    private fun assertCartesianFormula(
        traces: List<SummaryTrace>,
        mode: String,
        requestedFinalCount: Int = 2,
        alternativesPerFinal: Int,
        traceCount: Int,
    ) {
        assertEquals(traceCount, traces.size, "$mode Cartesian trace count")
        assertTrue(traces.all { it.final.edges.size == requestedFinalCount })

        val alternativesByFinal = traces
            .flatMap { it.final.edges }
            .groupBy(TraceEdge::fact)
            .mapValues { (_, edges) -> edges.toSet() }
        assertEquals(requestedFinalCount, alternativesByFinal.size)
        assertTrue(alternativesByFinal.values.all { it.size == alternativesPerFinal })
        assertEquals(traceCount, traces.mapTo(hashSetOf()) { it.final.edges }.size)
    }

    private data class RuleActionEvidence(
        val rule: CommonTaintConfigurationItem,
        val actions: Set<CommonTaintAction>,
    )

    private data class FullTraceEvidence(
        val starts: Set<TraceEntry.StartTraceEntry>,
        val actionStatements: Set<CommonInst>,
        val ruleActions: Set<RuleActionEvidence>,
    )

    private fun fullTraceEvidence(traces: List<FullStart2FinalTrace>): FullTraceEvidence {
        val actionStatements = linkedSetOf<CommonInst>()
        val ruleActions = linkedSetOf<RuleActionEvidence>()

        fun collectAction(action: TraceEntryAction?) {
            when (action) {
                is TraceEntryAction.CallRuleAction -> {
                    ruleActions += RuleActionEvidence(action.rule, action.action)
                }

                is TraceEntryAction.SequentialSourceRule -> {
                    ruleActions += RuleActionEvidence(action.rule, action.action)
                }

                else -> Unit
            }
        }

        for (trace in traces) {
            val start = trace.startEntry as? TraceEntry.SourceStartEntry
            collectAction(start?.sourcePrimaryAction)
            start?.sourceOtherActions?.forEach(::collectAction)

            for (entry in trace.actionVariants.int2ObjectEntrySet()) {
                actionStatements += trace.entries[entry.intKey].statement
                for (variant in entry.value) {
                    collectAction(variant.primaryAction)
                    variant.otherActions.forEach(::collectAction)
                }
            }
        }

        return FullTraceEvidence(
            starts = traces.mapTo(linkedSetOf()) { it.startEntry },
            actionStatements = actionStatements,
            ruleActions = ruleActions,
        )
    }
}
