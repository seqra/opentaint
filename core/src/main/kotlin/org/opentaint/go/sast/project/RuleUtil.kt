package org.opentaint.go.sast.project

import org.opentaint.common.sast.ProjectAnalyzer.PreloadedRules
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.dataflow.go.rules.GoCombinedTaintRulesProvider
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
import org.opentaint.go.config.GoConfigLoader
import org.opentaint.semgrep.go.pattern.conversion.toGoSerializedTaintConfig

fun PreloadedRules<GoSerializedItem, GoSerializedTaintConfig>.loadRules(): GoTaintRulesProvider {
    val userConfig = GoTaintConfiguration()
    GoConfigLoader.getConfig()?.let { userConfig.loadConfig(it) }

    rules.forEach {
        userConfig.loadConfig(it.toGoSerializedTaintConfig())
    }

    if (customApproximationConfig.isEmpty()) return userConfig

    val approxConfig = GoTaintConfiguration()
    customApproximationConfig.forEach { approxConfig.loadConfig(it) }
    return GoCombinedTaintRulesProvider(userConfig, approxConfig)
}
