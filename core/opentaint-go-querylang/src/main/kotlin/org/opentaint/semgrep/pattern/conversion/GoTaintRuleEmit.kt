package org.opentaint.semgrep.pattern.conversion

import org.opentaint.dataflow.configuration.go.serialized.GoSerializedGlobalSource
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep

fun TaintRuleFromSemgrep<GoSerializedItem>.toGoSerializedTaintConfig(): GoSerializedTaintConfig {
    val items = taintRules.flatMap { it.rules }
    return GoSerializedTaintConfig(
        globalSource = items.filterIsInstance<GoSerializedGlobalSource>(),
        source = items.filterIsInstance<GoSerializedRule.Source>(),
        sink = items.filterIsInstance<GoSerializedRule.Sink>(),
        passThrough = items.filterIsInstance<GoSerializedRule.PassThrough>(),
        cleaner = items.filterIsInstance<GoSerializedRule.Cleaner>(),
    )
}

fun TaintRuleFromSemgrep<GoSerializedItem>.toGoTaintConfiguration(): GoTaintConfiguration =
    GoTaintConfiguration().also { it.loadConfig(toGoSerializedTaintConfig()) }
