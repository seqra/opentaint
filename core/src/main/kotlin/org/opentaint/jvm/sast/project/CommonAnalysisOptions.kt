package org.opentaint.jvm.sast.project

import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta.Severity
import org.opentaint.jvm.sast.dataflow.DebugOptions
import java.nio.file.Path
import kotlin.time.Duration

data class CommonAnalysisOptions(
    val customApproximationConfig: List<Path> = emptyList(),
    val semgrepRuleSet: List<Path> = emptyList(),
    val semgrepRuleLoadTrace: Path? = null,
    val semgrepSeverity: List<Severity> = emptyList(),
    val semgrepRuleId: List<String> = emptyList(),
    val trackExternalMethods: Boolean = false,
    val ifdsAnalysisTimeout: Duration = Duration.ZERO,
    val ifdsApMode: ApMode = ApMode.Tree,
    val debugOptions: DebugOptions? = null,
    val sarifGenerationOptions: SarifGenerationOptions = SarifGenerationOptions(),
)
