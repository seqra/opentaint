package org.opentaint.common.sast.rules

import mu.KLogging
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep.Structure
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep.TaintRuleGroup

abstract class SemgrepRuleProvider<RuleItem, ResolvedRule>(
    val rules: List<TaintRuleFromSemgrep<RuleItem>>
) {
    private var ruleIdFilter: Set<String>? = null

    fun selectRelevantSemgrepRules(ruleIds: Set<String>) {
        ruleIdFilter = rules
            .flatMapTo(hashSetOf()) { rule -> reduce(rule.root, ruleIds).retainedRuleIds }

        logger.debug { "Select ${ruleIdFilter?.size} from ${rules.sumOf { it.size }} rules" }
    }

    private data class Reduction(
        val applicable: Boolean,
        val retainedRuleIds: Set<String>,
    )

    private fun reduce(structure: Structure<RuleItem>, selectedRuleIds: Set<String>): Reduction =
        when (structure) {
            is Structure.Matching -> reduceMatching(structure.groups, selectedRuleIds)
            is Structure.Taint -> reduceTaint(structure, selectedRuleIds)
            is Structure.Join -> reduceJoin(structure, selectedRuleIds)
        }

    private fun reduceMatching(
        groups: List<TaintRuleGroup<RuleItem>>,
        selectedRuleIds: Set<String>,
    ): Reduction {
        val applicableGroups = groups.map { reduceGroup(it, selectedRuleIds) }.filter { it.applicable }
        return Reduction(
            applicable = applicableGroups.isNotEmpty(),
            retainedRuleIds = applicableGroups.flatMapTo(hashSetOf()) { it.retainedRuleIds },
        )
    }

    private fun reduceTaint(
        structure: Structure.Taint<RuleItem>,
        selectedRuleIds: Set<String>,
    ): Reduction {
        val sources = structure.sources.map { reduceGroup(it, selectedRuleIds) }.filter { it.applicable }
        if (structure.sources.isNotEmpty() && sources.isEmpty()) return Reduction(false, emptySet())

        val sinks = structure.sinks.map { reduceGroup(it, selectedRuleIds) }.filter { it.applicable }
        if (structure.sinks.isNotEmpty() && sinks.isEmpty()) return Reduction(false, emptySet())

        val otherGroups = (structure.propagators + structure.sanitizers)
            .map { reduceGroup(it, selectedRuleIds) }
            .filter { it.applicable }
        return Reduction(
            applicable = true,
            retainedRuleIds = (sources + sinks + otherGroups)
                .flatMapTo(hashSetOf()) { it.retainedRuleIds },
        )
    }

    private fun reduceJoin(
        structure: Structure.Join<RuleItem>,
        selectedRuleIds: Set<String>,
    ): Reduction {
        val retainedRuleIds = hashSetOf<String>()
        var applicable = false
        structure.branches.forEach { branch ->
            val right = reduce(branch.rightOperand.child, selectedRuleIds)
            if (!right.applicable) return@forEach

            val left = branch.leftOperands
                .map { reduce(it.child, selectedRuleIds) }
                .filter { it.applicable }
            if (left.isEmpty()) return@forEach

            applicable = true
            retainedRuleIds += right.retainedRuleIds
            left.forEach { retainedRuleIds += it.retainedRuleIds }
        }
        return Reduction(applicable, retainedRuleIds)
    }

    private fun reduceGroup(
        group: TaintRuleGroup<RuleItem>,
        selectedRuleIds: Set<String>,
    ): Reduction {
        val candidates = group.rules.mapNotNull { it.ruleItemId() }.filterTo(hashSetOf()) { it in selectedRuleIds }
        val applicableRuleIds = candidates
            .filterTo(hashSetOf()) { group.ruleDependencies[it].isNullOrEmpty() }
        val dependentsByRuleId = hashMapOf<String, MutableSet<String>>()
        candidates.forEach { ruleId ->
            group.ruleDependencies[ruleId].orEmpty().forEach { dependencyId ->
                dependentsByRuleId.getOrPut(dependencyId) { hashSetOf() }.add(ruleId)
            }
        }

        val worklist = ArrayDeque(applicableRuleIds)
        while (worklist.isNotEmpty()) {
            val applicableRuleId = worklist.removeFirst()
            dependentsByRuleId[applicableRuleId].orEmpty().forEach { dependentId ->
                if (applicableRuleIds.add(dependentId)) {
                    worklist.addLast(dependentId)
                }
            }
        }

        return Reduction(
            applicable = group.finalRuleIds.any { it in applicableRuleIds },
            retainedRuleIds = applicableRuleIds,
        )
    }

    abstract fun RuleItem.ruleItemId(): String?
    abstract fun ResolvedRule.resolvedRuleId(): String?

    fun <T : ResolvedRule> Iterable<T>.select(allRelevant: Boolean): Iterable<T> {
        if (allRelevant) return this
        val selectedRuleIds = ruleIdFilter ?: return this
        return filter { rule ->
            val rId = rule.resolvedRuleId() ?: return@filter true
            selectedRuleIds.contains(rId)
        }
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}
