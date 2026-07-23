package org.opentaint.semgrep.pattern

import org.opentaint.dataflow.configuration.jvm.serialized.SerializedFieldRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedItem
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

data class TaintRuleFromSemgrep<R>(
    val ruleId: String,
    val root: Structure<R>,
) {
    val taintRules: List<TaintRuleGroup<R>> get() = root.flatten()
    val size: Int get() = taintRules.sumOf { it.size }

    sealed interface Structure<R> {
        fun flatten(): List<TaintRuleGroup<R>>

        data class Matching<R>(val groups: List<TaintRuleGroup<R>>) : Structure<R> {
            override fun flatten(): List<TaintRuleGroup<R>> = groups
        }

        data class Taint<R>(
            val sources: List<TaintRuleGroup<R>>,
            val sinks: List<TaintRuleGroup<R>>,
            val propagators: List<TaintRuleGroup<R>>,
            val sanitizers: List<TaintRuleGroup<R>>,
        ) : Structure<R> {
            override fun flatten(): List<TaintRuleGroup<R>> = sources + sinks + propagators + sanitizers
        }

        data class Join<R>(val branches: List<JoinBranch<R>>) : Structure<R> {
            override fun flatten(): List<TaintRuleGroup<R>> = branches.flatMap { it.flatten() }
        }
    }

    data class JoinBranch<R>(
        val leftOperands: List<JoinOperand<R>>,
        val rightOperand: JoinOperand<R>,
    ) {
        fun flatten() = leftOperands.flatMap { it.flatten() } + rightOperand.flatten()
    }

    data class JoinOperand<R>(
        val itemId: String,
        val ruleId: String,
        val metavar: String,
        val child: Structure<R>,
    ) {
        fun flatten() = child.flatten()
    }

    data class TaintRuleGroup<R>(
        val rules: List<R>,
        val ruleDependencies: Map<String, Set<String>> = emptyMap(),
        val finalRuleIds: Set<String> = emptySet(),
    ) {
        val size: Int get() = rules.size
    }
}

fun TaintRuleFromSemgrep<SerializedItem>.createTaintConfig(): SerializedTaintConfig {
    val rules = taintRules.flatMap { it.rules }
    return SerializedTaintConfig(
        entryPoint = rules.filterIsInstance<SerializedRule.EntryPoint>(),
        source = rules.filterIsInstance<SerializedRule.Source>(),
        methodExitSource = rules.filterIsInstance<SerializedRule.MethodExitSource>(),
        sink = rules.filterIsInstance<SerializedRule.Sink>(),
        passThrough = rules.filterIsInstance<SerializedRule.PassThrough>(),
        cleaner = rules.filterIsInstance<SerializedRule.Cleaner>(),
        methodExitSink = rules.filterIsInstance<SerializedRule.MethodExitSink>(),
        methodEntrySink = rules.filterIsInstance<SerializedRule.MethodEntrySink>(),
        staticFieldSource = rules.filterIsInstance<SerializedFieldRule.SerializedStaticFieldSource>(),
    )
}
