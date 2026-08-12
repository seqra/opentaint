package org.opentaint.dataflow.ap.ifds.taint

import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.concurrent.ConcurrentHashMap

typealias ActionableRules =
    Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>

/**
 * Experimental record of source actions that emitted at least one fact during
 * the normal forward analysis.
 *
 * This is deliberately only an observation mechanism. Production actionable
 * rule selection continues to use trace resolution.
 */
class ForwardActionableRulesRecorder {
    private var rules = ConcurrentHashMap<
        CommonInst,
        ConcurrentHashMap<CommonTaintConfigurationItem, MutableSet<CommonTaintAction>>
        >()

    fun record(
        statement: CommonInst,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
    ) {
        rules.computeIfAbsent(statement) { ConcurrentHashMap() }
            .computeIfAbsent(rule) { ConcurrentHashMap.newKeySet() }
            .add(action)
    }

    fun reset() {
        rules = ConcurrentHashMap()
    }

    fun snapshot(): ActionableRules = rules.mapValues { (_, statementRules) ->
        statementRules.mapValues { (_, actions) -> actions.toSet() }
    }
}

object ForwardActionableRulesExperiment {
    const val PROPERTY = "opentaint.experimental.forward-actionable-rules"

    val enabled: Boolean by lazy {
        System.getProperty(PROPERTY)?.toBooleanStrictOrNull() == true
    }
}
