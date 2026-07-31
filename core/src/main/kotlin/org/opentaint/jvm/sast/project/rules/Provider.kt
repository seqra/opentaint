package org.opentaint.jvm.sast.project.rules

import org.opentaint.common.sast.ProjectAnalyzerBase.PreloadedRules
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedItem
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.ir.api.jvm.JIRClasspath
import org.opentaint.jvm.sast.dataflow.JIRCombinedTaintRulesProvider
import org.opentaint.jvm.sast.dataflow.JIRCombinedTaintRulesProvider.CombinationMode
import org.opentaint.jvm.sast.dataflow.JIRCombinedTaintRulesProvider.CombinationOptions
import org.opentaint.jvm.sast.dataflow.JIRMethodExitRuleProvider
import org.opentaint.jvm.sast.dataflow.JIRMethodGetDefaultProvider
import org.opentaint.jvm.sast.dataflow.JIRTaintRulesProvider
import org.opentaint.jvm.sast.dataflow.rules.TaintConfiguration
import org.opentaint.jvm.sast.project.ProjectAnalysisContext
import org.opentaint.jvm.sast.project.spring.SpringRuleProvider
import org.opentaint.jvm.sast.rules.JIRSemgrepRuleProvider
import org.opentaint.jvm.sast.util.locationChecker

fun loadTaintConfig(
    cp: JIRClasspath,
    rules: PreloadedRules<SerializedItem, SerializedTaintConfig>
): TaintRulesProvider {
    val config = TaintConfiguration(cp)
    config.loadConfig(rules.defaultConfig)
    return JIRSemgrepRuleProvider(rules.rules, config).withApproximationConfigs(cp, rules.customApproximationConfig)
}

val approximationConfigCombinationOptions = CombinationOptions(
    entryPoint = CombinationMode.IGNORE,
    source = CombinationMode.IGNORE,
    sink = CombinationMode.IGNORE,
    cleaner = CombinationMode.IGNORE,
    passThrough = CombinationMode.OVERRIDE,
)

fun TaintRulesProvider.withApproximationConfigs(
    cp: JIRClasspath,
    approximationConfigs: List<SerializedTaintConfig>,
): TaintRulesProvider {
    if (approximationConfigs.isEmpty()) return this

    val approximationsConfig = TaintConfiguration(cp)
    approximationConfigs.forEach { approximationsConfig.loadConfig(it) }

    return JIRCombinedTaintRulesProvider(
        this, JIRTaintRulesProvider(approximationsConfig),
        approximationConfigCombinationOptions,
    )
}

fun ProjectAnalysisContext.analysisConfig(initialConfig: TaintRulesProvider): TaintRulesProvider {
    var config = initialConfig
    config = JIRMethodExitRuleProvider(config)
    config = JIRMethodGetDefaultProvider(config, projectClasses.locationChecker())
    if (springWebProjectContext != null) {
        config = SpringRuleProvider(config, springWebProjectContext)
    }
    return config
}
