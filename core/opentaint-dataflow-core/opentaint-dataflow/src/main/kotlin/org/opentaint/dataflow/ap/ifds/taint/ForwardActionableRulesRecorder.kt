package org.opentaint.dataflow.ap.ifds.taint

import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.concurrent.ConcurrentHashMap

typealias ActionableRules =
    Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>

/** Source actions that emitted at least one fact during forward analysis. */
class ForwardActionableRulesRecorder {
    private val rules = ConcurrentHashMap<
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

    fun clear() = rules.clear()

    fun snapshot(): ActionableRules = rules.mapValues { (_, statementRules) ->
        statementRules.mapValues { (_, actions) -> actions.toSet() }
    }

    fun collectInto(
        collector: MutableMap<CommonInst, MutableMap<CommonTaintConfigurationItem, MutableSet<CommonTaintAction>>>,
    ) {
        rules.forEach { (statement, statementRules) ->
            val targetRules = collector.getOrPut(statement, ::hashMapOf)
            statementRules.forEach { (rule, actions) ->
                targetRules.getOrPut(rule, ::hashSetOf).addAll(actions)
            }
        }
    }
}
