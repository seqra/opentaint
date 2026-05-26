package org.opentaint

import org.opentaint.dataflow.configuration.go.serialized.GoSerializedGlobalSource
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep

class GoTaintRuleEmitter {
    fun emit(rule: TaintRuleFromSemgrep<GoSerializedItem>): GoTaintConfiguration =
        GoTaintConfiguration().also { it.loadConfig(buildSerializedConfig(rule)) }

    fun buildSerializedConfig(rule: TaintRuleFromSemgrep<GoSerializedItem>): GoSerializedTaintConfig {
        val items = rule.taintRules.flatMap { it.rules }
        return GoSerializedTaintConfig(
            globalSource = items.filterIsInstance<GoSerializedGlobalSource>(),
            source = items.filterIsInstance<GoSerializedRule.Source>(),
            sink = items.filterIsInstance<GoSerializedRule.Sink>(),
            passThrough = items.filterIsInstance<GoSerializedRule.PassThrough>(),
            cleaner = items.filterIsInstance<GoSerializedRule.Cleaner>(),
        )
    }
}
