package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCleanAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedGlobalSource
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedPassAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.dataflow.configuration.isFalse
import org.opentaint.dataflow.go.GoFunctionSignature
import java.util.concurrent.atomic.AtomicInteger

class GoTaintConfiguration {
    private val globalSourceSimple = hashMapOf<String, MutableList<GoSerializedGlobalSource>>()
    private val globalSourcePatterns = mutableListOf<GoSerializedGlobalSource>()
    private val globalSourceMemo = hashMapOf<String, List<TaintRule.GlobalReadSource>>()

    private val sourceSimple = hashMapOf<String, MutableList<GoSerializedRule.Source>>()
    private val sourcePatterns = mutableListOf<GoSerializedRule.Source>()
    private val sourceMemo = hashMapOf<String, List<TaintRule.Source>>()

    private val sinkSimple = hashMapOf<String, MutableList<GoSerializedRule.Sink>>()
    private val sinkPatterns = mutableListOf<GoSerializedRule.Sink>()
    private val sinkMemo = hashMapOf<String, List<TaintRule.Sink>>()

    private val passSimple = hashMapOf<String, MutableList<GoSerializedRule.PassThrough>>()
    private val passPatterns = mutableListOf<GoSerializedRule.PassThrough>()
    private val passMemo = hashMapOf<String, List<TaintRule.PassThrough>>()

    private val cleanerSimple = hashMapOf<String, MutableList<GoSerializedRule.Cleaner>>()
    private val cleanerPatterns = mutableListOf<GoSerializedRule.Cleaner>()
    private val cleanerMemo = hashMapOf<String, List<TaintRule.Cleaner>>()

    private val ruleIdGen = AtomicInteger()

    @Synchronized
    fun loadConfig(config: GoSerializedTaintConfig) {
        config.globalSource.forEach { addRule(it) }
        config.source.forEach { addRule(it) }
        config.sink.forEach { addRule(it) }
        config.passThrough.forEach { addRule(it) }
        config.cleaner.forEach { addRule(it) }

        // Invalidate memo: any subsequent lookup must re-resolve.
        globalSourceMemo.clear()
        sourceMemo.clear()
        sinkMemo.clear()
        passMemo.clear()
        cleanerMemo.clear()
    }

    private fun addRule(rule: GoSerializedGlobalSource) {
        when (val gv = rule.global) {
            is GoNameMatcher.Simple -> globalSourceSimple.getOrPut(gv.name, ::mutableListOf).add(rule)
            is GoNameMatcher.Pattern -> globalSourcePatterns.add(rule)
        }
    }

    private fun addRule(rule: GoSerializedRule.Source) {
        when (val fn = rule.function) {
            is GoNameMatcher.Simple -> sourceSimple.getOrPut(fn.name, ::mutableListOf).add(rule)
            is GoNameMatcher.Pattern -> sourcePatterns.add(rule)
        }
    }

    private fun addRule(rule: GoSerializedRule.Sink) {
        when (val fn = rule.function) {
            is GoNameMatcher.Simple -> sinkSimple.getOrPut(fn.name, ::mutableListOf).add(rule)
            is GoNameMatcher.Pattern -> sinkPatterns.add(rule)
        }
    }

    private fun addRule(rule: GoSerializedRule.PassThrough) {
        when (val fn = rule.function) {
            is GoNameMatcher.Simple -> passSimple.getOrPut(fn.name, ::mutableListOf).add(rule)
            is GoNameMatcher.Pattern -> passPatterns.add(rule)
        }
    }

    private fun addRule(rule: GoSerializedRule.Cleaner) {
        when (val fn = rule.function) {
            is GoNameMatcher.Simple -> cleanerSimple.getOrPut(fn.name, ::mutableListOf).add(rule)
            is GoNameMatcher.Pattern -> cleanerPatterns.add(rule)
        }
    }

    @Synchronized
    fun sourceForGlobal(name: String): List<TaintRule.GlobalReadSource> = globalSourceMemo.getOrPut(name) {
        candidates(name, globalSourceSimple, globalSourcePatterns, { global })
            .mapNotNull { specialize(it, name) }
    }

    @Synchronized
    fun sourceForFunction(signature: GoFunctionSignature, allRelevant: Boolean): List<TaintRule.Source> = sourceMemo.getOrPut(signature.name) {
        candidates(signature, sourceSimple, sourcePatterns).mapNotNull { specialize(it, signature) }
    }

    @Synchronized
    fun sinkForFunction(signature: GoFunctionSignature): List<TaintRule.Sink> = sinkMemo.getOrPut(signature.name) {
        candidates(signature, sinkSimple, sinkPatterns).mapNotNull { specialize(it, signature) }
    }

    @Synchronized
    fun passThroughForFunction(signature: GoFunctionSignature): List<TaintRule.PassThrough> = passMemo.getOrPut(signature.name) {
        candidates(signature, passSimple, passPatterns).mapNotNull { specialize(it, signature) }
    }

    @Synchronized
    fun cleanerForFunction(signature: GoFunctionSignature, allRelevant: Boolean): List<TaintRule.Cleaner> = cleanerMemo.getOrPut(signature.name) {
        candidates(signature, cleanerSimple, cleanerPatterns).mapNotNull { specialize(it, signature) }
    }

    private fun <R : GoSerializedRule> candidates(
        sig: GoFunctionSignature,
        simpleByName: Map<String, List<R>>,
        patternRules: List<R>,
    ): List<R> = candidates(sig.name, simpleByName, patternRules) { function }

    private fun <R> candidates(
        name: String,
        simpleByName: Map<String, List<R>>,
        patternRules: List<R>,
        ruleNameMatcher: R.() -> GoNameMatcher,
    ): List<R> {
        val direct = simpleByName[name].orEmpty()
        val patternMatches = patternRules.filter { it.ruleNameMatcher().matches(name) }
        if (patternMatches.isEmpty()) return direct
        if (direct.isEmpty()) return patternMatches
        return direct + patternMatches
    }

    private fun specialize(rule: GoSerializedGlobalSource, name: String): TaintRule.GlobalReadSource? {
        TODO()
    }

    private fun specialize(rule: GoSerializedRule.Source, signature: GoFunctionSignature): TaintRule.Source? {
        val condition = rule.condition.resolveToRuleCondition(signature)
        if (condition.isFalse()) return null

        val actions = rule.taint.flatMap { t ->
            t.pos.resolve(signature).map { GoAssignMark(t.kind, it) }
        }
        return TaintRule.Source(signature.name, condition, actions)
    }

    private fun specialize(rule: GoSerializedRule.Sink, signature: GoFunctionSignature): TaintRule.Sink? {
        val condition = rule.condition.resolveToRuleCondition(signature)
        if (condition.isFalse()) return null

        val trackFacts = rule.trackFactsReachAnalysisEnd
            .orEmpty()
            .flatMap { a ->
                a.pos.resolve(signature).map { GoAssignMark(a.kind, it) }
            }

        val id = rule.id ?: generateRuleId(rule)
        val meta = rule.meta ?: defaultMeta(signature.name)

        return TaintRule.Sink(signature.name, condition, trackFacts, id, meta)
    }

    private fun specialize(rule: GoSerializedRule.PassThrough, signature: GoFunctionSignature): TaintRule.PassThrough? {
        val actions = rule.copy.flatMap { it.toTaintAction(signature) }
        return TaintRule.PassThrough(signature.name, actions)
    }

    private fun specialize(rule: GoSerializedRule.Cleaner, signature: GoFunctionSignature): TaintRule.Cleaner? {
        val condition = rule.condition.resolveToRuleCondition(signature)
        if (condition.isFalse()) return null

        val actions = rule.cleans.flatMap { it.toTaintAction(signature) }
        return TaintRule.Cleaner(signature.name, condition, actions)
    }

    private fun GoSerializedPassAction.toTaintAction(signature: GoFunctionSignature): List<GoTaintAction> =
        from.resolve(signature).flatMap { f ->
            to.resolve(signature).map { t ->
                val kind = taintKind
                if (kind == null) CopyData(f, t) else CopyTaintMark(kind, f, t)
            }
        }

    private fun GoSerializedCleanAction.toTaintAction(signature: GoFunctionSignature): List<GoTaintAction> =
        pos.resolve(signature).map {
            val kind = taintKind
            if (kind == null) RemoveAllMarks(it) else RemoveMark(kind, it)
        }

    private fun generateRuleId(rule: GoSerializedRule.Sink): String {
        rule.meta?.cwe?.firstOrNull()?.let { return "CWE-$it" }
        return "go-generated-id-${ruleIdGen.incrementAndGet()}"
    }

    private fun defaultMeta(function: String): CommonTaintConfigurationSinkMeta =
        TaintRule.Sink.DefaultMeta("Taint sink: $function")
}
