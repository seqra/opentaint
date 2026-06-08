package org.opentaint.semgrep.go.pattern.conversion

import org.opentaint.dataflow.configuration.go.serialized.GoSerializedFieldSource
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
        fieldSource = items.filterIsInstance<GoSerializedFieldSource>(),
        source = items.filterIsInstance<GoSerializedRule.Source>(),
        sink = items.filterIsInstance<GoSerializedRule.Sink>(),
        passThrough = items.filterIsInstance<GoSerializedRule.PassThrough>(),
        cleaner = items.filterIsInstance<GoSerializedRule.Cleaner>(),
    )
}

fun GoTaintConfiguration.loadGoTaintConfiguration(semgrep: TaintRuleFromSemgrep<GoSerializedItem>): GoTaintConfiguration =
    this.also { it.loadConfig(semgrep.toGoSerializedTaintConfig()) }
