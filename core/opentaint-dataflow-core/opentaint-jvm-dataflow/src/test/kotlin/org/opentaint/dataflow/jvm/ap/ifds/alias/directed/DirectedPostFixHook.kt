package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.jvm.ap.ifds.AliasAnalysisMode
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JApplicationGraph
import java.util.concurrent.ConcurrentHashMap
import kotlin.test.assertNotNull

/** The analyses with a passed check: the entry point, the parameters and the rules. */
private val checkedAnalyses = ConcurrentHashMap.newKeySet<Triple<JIRInst, JIRLocalAliasAnalysis.Params, Any?>>()

/**
 * The post-fixpoint check (IMPL §9.1 item 3) of a facade test in `DIRECTED` mode. Call it with the
 * arguments of the facade before the facade is made. If [params] select the directed analysis, it
 * runs the analysis of the method one time with the check: a violation fails the test, and a result
 * that the time limit or the cancellation stops also fails it. The check runs one time for each
 * entry point, parameters and rules. The facade itself does not change.
 */
fun checkDirectedPostFix(
    entryPoint: JIRInst,
    graph: JApplicationGraph,
    callResolver: JIRCallResolver,
    rules: TaintRulesProvider?,
    reachability: JIRLocalVariableReachability,
    cancellation: Cancellation,
    languageManager: JIRLanguageManager,
    params: JIRLocalAliasAnalysis.Params,
) {
    if (params.mode != AliasAnalysisMode.DIRECTED || !params.useAliasAnalysis) return
    if (!checkedAnalyses.add(Triple(entryPoint, params, rules))) return
    val analysis = JIRDirectedAliasAnalysis(
        entryPoint, graph, callResolver, rules, reachability, cancellation, languageManager, params,
        verifyPostFix = true,
    )
    assertNotNull(analysis.compute(), "no directed result for ${entryPoint.location.method} (time limit or cancellation)")
}
