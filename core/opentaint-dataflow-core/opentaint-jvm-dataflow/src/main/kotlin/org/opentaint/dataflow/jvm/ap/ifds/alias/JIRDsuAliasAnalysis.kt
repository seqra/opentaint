package org.opentaint.dataflow.jvm.ap.ifds.alias

import org.opentaint.dataflow.ap.ifds.analysis.alias.AAHeapAccessor
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisResult
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.LocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.Params
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRIntraProcAliasAnalysis.Convert.convertToAliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JApplicationGraph

/**
 * The DSU alias analysis of main. It is the `DSU` backend of [org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis].
 * Its logic does not change.
 */
internal class JIRDsuAliasAnalysis(
    private val entryPoint: JIRInst,
    private val graph: JApplicationGraph,
    private val callResolver: JIRCallResolver,
    private val modelProvider: TaintRulesProvider?,
    private val localVariableReachability: JIRLocalVariableReachability,
    private val cancellation: Cancellation,
    private val languageManager: JIRLanguageManager,
    private val params: Params,
) : LocalAliasAnalysis<AliasInfo, AliasAccessor>() {
    override fun getInstIndex(statement: CommonInst): Int =
        languageManager.getInstIndex(statement)

    override fun localInfo(localIdx: Int): AAInfo =
        LocalAlias.SimpleLoc(RefValue.Local(localIdx, ContextInfo.rootContext))

    override fun convertAliasAccessor(aa: AliasAccessor): List<AAHeapAccessor> = when (aa) {
        is AliasAccessor.Array -> listOf(ArrayAlias)
        is AliasAccessor.Field -> listOf(FieldAlias(aa, false), FieldAlias(aa, true))
        is AliasAccessor.Static -> emptyList()
    }

    override fun convert(
        info: AAInfo,
        depth: Int,
        convertInstance: (Int) -> List<AliasInfo>
    ): List<AliasInfo> = info.convertToAliasInfo(depth, null, convertInstance)

    override fun compute(): AnalysisResult? {
        val analysis = JIRIntraProcAliasAnalysis(
            entryPoint, graph, callResolver,
            TaintRulesCallModelProvider(modelProvider),
            languageManager, cancellation, params
        )
        return analysis.compute(localVariableReachability)
    }
}
