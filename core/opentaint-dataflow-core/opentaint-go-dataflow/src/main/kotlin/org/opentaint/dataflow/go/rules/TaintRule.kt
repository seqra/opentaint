package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintAssignAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta.Severity
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSource
import org.opentaint.dataflow.configuration.jvm.serialized.ItemInfo

sealed interface TaintRule: CommonTaintConfigurationItem {
    val info: ItemInfo?

    data class GlobalReadSource(
        val global: String,
        val condition: CommonCondition<GoRuleCondition>,
        val actionsAfter: List<GoAssignMark>,
        override val info: ItemInfo?,
    ) : TaintRule, CommonTaintConfigurationSource, CommonTaintAssignAction

    data class Source(
        val function: String,
        val condition: CommonCondition<GoRuleCondition>,
        val actionsAfter: List<GoAssignMark>,
        override val info: ItemInfo?,
    ) : TaintRule, CommonTaintConfigurationSource, CommonTaintAssignAction

    data class Sink(
        val function: String,
        val condition: CommonCondition<GoRuleCondition>,
        val trackFactsReachAnalysisEnd: List<GoAssignMark>,
        override val id: String,
        override val meta: CommonTaintConfigurationSinkMeta,
        override val info: ItemInfo?,
    ) : TaintRule, CommonTaintConfigurationSink {

        data class DefaultMeta(
            override val message: String,
            override val severity: Severity = Severity.Error,
        ) : CommonTaintConfigurationSinkMeta
    }

    data class PassThrough(
        val function: String,
        val actionsAfter: List<GoTaintAction>,
        override val info: ItemInfo?,
    ) : TaintRule, CommonTaintConfigurationItem, CommonTaintAction

    data class Cleaner(
        val function: String,
        val condition: CommonCondition<GoRuleCondition>,
        val actionsAfter: List<GoTaintAction>,
        override val info: ItemInfo?,
    ) : TaintRule, CommonTaintConfigurationItem, CommonTaintAction
}
