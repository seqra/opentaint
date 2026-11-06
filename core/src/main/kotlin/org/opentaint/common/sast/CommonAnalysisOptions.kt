package org.opentaint.common.sast

import org.opentaint.common.sast.dataflow.DebugOptions
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.common.sast.sarif.SarifGenerationOptions
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.jvm.ap.ifds.AliasAnalysisMode
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import java.nio.file.Path
import kotlin.time.Duration

data class CommonAnalysisOptions(
    val customApproximationConfig: List<Path> = emptyList(),
    val semgrepRuleSet: List<Path> = emptyList(),
    val semgrepRuleLoadTrace: Path? = null,
    val semgrepSeverity: List<CommonTaintConfigurationSinkMeta.Severity> = emptyList(),
    val semgrepRuleId: List<String> = emptyList(),
    val semgrepRuleIdExclude: List<String> = emptyList(),
    val trackExternalMethods: Boolean = false,
    val ifdsAnalysisTimeout: Duration = Duration.ZERO,
    val ifdsApMode: ApMode = ApMode.Tree,
    val debugOptions: DebugOptions? = null,
    val sarifGenerationOptions: SarifGenerationOptions = SarifGenerationOptions(),
    val cwe: List<Int> = emptyList(),
    val useSymbolicExecution: Boolean = false,
    val symbolicExecutionTimeout: Duration = Duration.ZERO,
    val storeSummaries: Boolean = false,
    val experimentalAAInterProcCallDepth: Int = 1,
    val experimentalAliasAnalysisMode: AliasAnalysisMode = AliasAnalysisMode.DSU,
    val experimentalAliasSymbolicDepth: Int = JIRLocalAliasAnalysis.Params().symDepth,
    val experimentalAliasMaxAccessors: Int = JIRLocalAliasAnalysis.Params().maxAccessors,
    val experimentalAliasStatistics: Boolean = false,
) {
    val summariesApMode get() = ifdsApMode.takeIf { storeSummaries }

    fun taintAnalyzerOptions() = TaintAnalyzerOptions(
        ifdsTimeout = ifdsAnalysisTimeout,
        ifdsApMode = ifdsApMode,
        symbolicExecutionEnabled = useSymbolicExecution,
        analysisCwe = cwe.takeIf { it.isNotEmpty() }?.toSet(),
        storeSummaries = storeSummaries,
        experimentalAAInterProcCallDepth = experimentalAAInterProcCallDepth,
        experimentalAliasAnalysisMode = experimentalAliasAnalysisMode,
        experimentalAliasSymbolicDepth = experimentalAliasSymbolicDepth,
        experimentalAliasMaxAccessors = experimentalAliasMaxAccessors,
        experimentalAliasStatistics = experimentalAliasStatistics,
        debugOptions = debugOptions,
        tracePathLimit = sarifGenerationOptions.sarifCodeFlowLimit,
    )
}
