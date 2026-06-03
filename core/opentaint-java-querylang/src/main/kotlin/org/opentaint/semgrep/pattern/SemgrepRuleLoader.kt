package org.opentaint.semgrep.pattern

import com.charleskorn.kaml.YamlMap
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta.Severity
import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.dataflow.jvm.ap.ifds.taint.PrimitiveTaintExt
import org.opentaint.semgrep.pattern.SemgrepTraceEntry.Step
import org.opentaint.semgrep.pattern.conversion.LanguageStrategy
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.SemgrepRuleAutomataBuilder
import org.opentaint.semgrep.pattern.conversion.taint.RuleConversionCtx
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataJoinMetaVarRef
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataJoinOperation
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataJoinRule
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataJoinRuleItem
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata
import org.opentaint.semgrep.pattern.conversion.taint.convertTaintAutomataJoinToTaintRules
import org.opentaint.semgrep.pattern.conversion.taint.convertTaintAutomataToTaintRules
import org.opentaint.semgrep.pattern.conversion.taint.createTaintAutomata
import java.nio.file.Path
import kotlin.io.path.Path

data class RuleMetadata(
    val ruleId: String,
    val shortRuleId: String,
    val message: String,
    val severity: Severity,
    val metadata: YamlMap?
)

private typealias BuiltRule = RuleWithMetaVars<TaintRegisterStateAutomata, ResolvedMetaVarInfo>

class SemgrepRuleLoader(
    strategies: List<LanguageStrategy<*, *>>
) {
    private val strategies: Map<String, LanguageStrategy<*, *>> =
        strategies.associateBy { it.language }

    private fun strategyFor(rule: SemgrepYamlRule): LanguageStrategy<*, *>? =
        rule.languages.orEmpty().firstNotNullOfOrNull { strategies[it.lowercase()] }

    private fun strategyFor(ruleInfo: RuleInfo): LanguageStrategy<*, *>? =
        ruleInfo.language?.let { strategies[it.lowercase()] }

    private fun <P : Any, R> automataBuilder(strategy: LanguageStrategy<P, R>) = SemgrepRuleAutomataBuilder(strategy)

    private data class RegisteredRule(
        val ruleId: String,
        val rule: SemgrepYamlRule,
        val pathInfo: RuleSetPathInfo,
        val ruleTrace: SemgrepRuleLoadTrace
    )

    private data class RuleSetPathInfo(
        val rulesRoot: Path,
        val ruleRelativePath: Path,
    )

    private val registeredRules = hashMapOf<String, RegisteredRule>()
    private val tagIndex = hashMapOf<String, MutableList<String>>()

    fun registerRuleSet(
        ruleSetText: String,
        ruleRelativePath: Path,
        rulesRoot: Path,
        trace: SemgrepLoadTrace,
    ) {
        val pathInfo = RuleSetPathInfo(rulesRoot, ruleRelativePath)
        val ruleSetName = pathInfo.ruleSetName()
        registerRuleSet(ruleSetText, ruleSetName, pathInfo, trace.fileTrace(ruleSetName))
    }

    private fun registerRuleSet(
        ruleSetText: String,
        ruleSetName: String,
        pathInfo: RuleSetPathInfo,
        semgrepFileTrace: SemgrepFileLoadTrace
    ) {
        val ruleSet = parseSemgrepYaml(ruleSetText, semgrepFileTrace) ?: return

        val (supportedRules, _) = ruleSet.rules.partition { it.isSupportedRule() }
        semgrepFileTrace.info("Found ${supportedRules.size} supported rules")

        supportedRules.forEach {
            val ruleId = SemgrepRuleUtils.getRuleId(ruleSetName, it.id)
            val trace = semgrepFileTrace.ruleTrace(ruleId, it.id)
            registerRule(RegisteredRule(ruleId, it, pathInfo, trace))
        }

        semgrepFileTrace.info("Register ${supportedRules.size} rules")
    }

    private fun buildTagIndex() {
        tagIndex.clear()
        for (registered in registeredRules.values) {
            for (tag in registered.rule.tags) {
                tagIndex.getOrPut(tag, ::mutableListOf).add(registered.ruleId)
            }
        }
    }

    private fun registerRule(rule: RegisteredRule) {
        if (rule.ruleId in registeredRules) {
            rule.ruleTrace.stepTrace(Step.LOAD_RULESET)
                .error(DuplicateRule(rule.ruleId))
            return
        }

        registeredRules[rule.ruleId] = rule
    }

    data class RuleLoadResult(
        val rulesWithMeta: List<Pair<TaintRuleFromSemgrep<*>, RuleMetadata>>,
        val disabledRules: Set<String>,
    )

    fun loadRules(severity: List<Severity> = emptyList(), ruleIdFilter: List<String> = emptyList()): RuleLoadResult {
        fun Rule<*>.skip(): Boolean =
            info.isDisabled || info.isLibraryRule
                || !ruleSeverityAllow(this, severity)
                || !ruleIdAllow(this, ruleIdFilter)

        registeredRules.values.toList()
            .forEach { parseRule(it, forceLibraryMode = false) }

        buildTagIndex()

        resolveRuleOverrides()

        parsedRules.values
            .filterIsInstance<NormalRule<Formula>>()
            .forEach { buildNormalRule(it) }

        val loaded = mutableListOf<Pair<TaintRuleFromSemgrep<*>, RuleMetadata>>()
        builtNormalRules.values
            .filterNot { it.skip() }
            .forEach {
                loaded += loadNormalRule(it) ?: return@forEach
            }

        parsedRules.values
            .filterIsInstance<JoinRule<*>>()
            .filterNot { it.skip() }
            .forEach {
                loaded += loadJoinRule(it) ?: return@forEach
            }

        return RuleLoadResult(loaded, disabledRules)
    }

    private data class RuleInfo(
        val ruleId: String,
        val shortRuleId: String,
        val language: String?,
        val primitiveTracking: Boolean,
        val overridesRuleId: String?,
        val isLibraryRule: Boolean,
        val isDisabled: Boolean,
        val metadata: RuleMetadata,
        val sinkMeta: SinkMetaData,
        val ruleTrace: SemgrepRuleLoadTrace,
        val pathInfo: RuleSetPathInfo,
    )

    private fun resolveRuleOverrides() {
        val overrideMapping = hashMapOf<String, String>()
        for ((ruleId, rule) in parsedRules) {
            val override = rule.info.overridesRuleId ?: continue
            val prev = overrideMapping.putIfAbsent(override, ruleId)
            if (prev != null) {
                registeredRules[ruleId]?.ruleTrace
                    ?.stepTrace(Step.LOAD_RULESET)
                    ?.error(AmbiguousOverride(currentRuleId = ruleId, previousRuleId = prev))
            }
        }

        for ((ruleId, overrideId) in overrideMapping) {
            val info = parsedRules[ruleId]?.info
            if (info == null) {
                registeredRules[overrideId]?.ruleTrace
                    ?.stepTrace(Step.LOAD_RULESET)
                    ?.error(RuleOverridesNothing(targetRuleId = ruleId))
                continue
            }
            parsedRules[ruleId] = RuleOverride(overrideId, info)
        }
    }

    private sealed interface Rule<P> {
        val info: RuleInfo
    }

    private data class NormalRule<P>(
        val rule: SemgrepRule<P>,
        override val info: RuleInfo
    ) : Rule<P>

    private data class JoinRule<P>(
        val refs: List<SemgrepYamlJoinRuleRef>,
        val on: List<SemgrepJoinRuleOn>,
        override val info: RuleInfo,
    ) : Rule<P>

    private data class RuleOverride<P>(
        val refId: String,
        override val info: RuleInfo
    ) : Rule<P>

    private val parsedRules = hashMapOf<String, Rule<Formula>>()

    private val disabledRules = hashSetOf<String>()

    private fun parseRule(registeredRule: RegisteredRule, forceLibraryMode: Boolean) {
        val ruleInfo = parseRuleInfo(registeredRule, forceLibraryMode)
        val loadTrace = ruleInfo.ruleTrace.stepTrace(Step.LOAD_RULESET)

        if (ruleInfo.isDisabled) {
            disabledRules.add(ruleInfo.ruleId)
            loadTrace.info("Skip disabled rule")
            return
        }

        val rule = registeredRule.rule
        when (rule.mode) {
            null, "search" -> {
                val parsed = parseMatchingRule(rule, loadTrace) ?: return
                addParsedRule(ruleInfo, NormalRule(parsed, ruleInfo), loadTrace)
            }

            "taint" -> {
                val parsed = parseTaintRule(rule, loadTrace)
                addParsedRule(ruleInfo, NormalRule(parsed, ruleInfo), loadTrace)
            }
            "join" -> {
                val joinRule = rule.join ?: run {
                    loadTrace.error(JoinRuleWithoutJoinSection())
                    return
                }

                val parsed = parseJoinRule(joinRule, loadTrace) ?: return

                val refs = parsed.refs.map { ref ->
                    val nestedRule = parsed.rules.firstOrNull { it.id == ref.rule }
                    if (nestedRule == null) return@map ref

                    val ruleSetName = registeredRule.pathInfo.ruleSetName()
                    val nestedRuleId = SemgrepRuleUtils.getRuleId(ruleSetName, nestedRule.id)
                    val nestedRegistered = RegisteredRule(
                        nestedRuleId, nestedRule, registeredRule.pathInfo, ruleInfo.ruleTrace
                    )
                    registerRule(nestedRegistered)
                    parseRule(nestedRegistered, forceLibraryMode = true)

                    ref.copy(rule = nestedRule.id)
                }

                val parsedJoin = JoinRule<Formula>(refs, parsed.on, ruleInfo)
                addParsedRule(ruleInfo, parsedJoin, loadTrace)
            }

            else -> {
                loadTrace.error(UnsupportedMode(rule.mode))
                return
            }
        }
    }

    private fun addParsedRule(ruleInfo: RuleInfo, rule: Rule<Formula>, trace: SemgrepRuleLoadStepTrace) {
        if (rule is NormalRule && rule.rule.isEmpty && !ruleInfo.isLibraryRule) {
            trace.error(EmptyRuleAfterParse())
            return
        }

        val id = ruleInfo.ruleId
        if (id in parsedRules) {
            trace.error(DuplicateRule(id))
            return
        }

        parsedRules[id] = rule
    }

    private val builtNormalRules = hashMapOf<String, NormalRule<BuiltRule>>()

    private fun buildNormalRule(rule: NormalRule<Formula>) {
        val trace = rule.info.ruleTrace

        val strategy =  strategyFor(rule.info) ?: return
        val ruleAutomataBuilder = automataBuilder(strategy)
        val ruleAutomata = runCatching {
            ruleAutomataBuilder.build(rule.rule, trace)
        }.onFailure { ex ->
            trace.stepTrace(Step.BUILD).error(FailedToBuildRuleAutomata(ex.message))
            return
        }.getOrThrow()

        val stats = ruleAutomataBuilder.stats
        if (stats.isFailure) {
            trace.stepTrace(Step.BUILD).error(AutomataBuildIssues())
        }

        val btaTrace = trace.stepTrace(Step.BUILD_TAINT_AUTOMATA)
        val taintAutomata = createTaintAutomata(ruleAutomata, btaTrace, strategy.typeOps)

        if (taintAutomata.isEmpty && !rule.info.isLibraryRule) {
            trace.stepTrace(Step.BUILD).error(EmptyRuleAfterBuild())
            return
        }

        builtNormalRules[rule.info.ruleId] = NormalRule(taintAutomata, rule.info)
    }

    private fun loadNormalRule(rule: NormalRule<BuiltRule>): Pair<TaintRuleFromSemgrep<*>, RuleMetadata>? {
        val trace = rule.info.ruleTrace

        val a2trTrace = trace.stepTrace(Step.AUTOMATA_TO_TAINT_RULE)
        val strategy = strategyFor(rule.info) ?: return null
        val typeOps = strategy.typeOps
        return runCatching {
            val ctx = RuleConversionCtx(rule.info.ruleId, rule.modeModifier(), rule.info.sinkMeta, a2trTrace, typeOps)
            val rules = convertNormalRuleWithStrategy(strategy, ctx, rule.rule)
            rules to rule.info.metadata
        }.onFailure { ex ->
            a2trTrace.error(FailedToCreateTaintRules(ex.message))
            return null
        }.getOrThrow().also {
            trace.info("Generate ${it.first.size} rules from ${it.first.ruleId}")
        }
    }

    private fun <P : Any, R> convertNormalRuleWithStrategy(
        strategy: LanguageStrategy<P, R>,
        ctx: RuleConversionCtx,
        rule: SemgrepRule<RuleWithMetaVars<TaintRegisterStateAutomata, ResolvedMetaVarInfo>>,
    ): TaintRuleFromSemgrep<R> = ctx.convertTaintAutomataToTaintRules(strategy.taintRuleStrategy, rule)

    private fun loadJoinRule(rule: JoinRule<*>): Pair<TaintRuleFromSemgrep<*>, RuleMetadata>? {
        val trace = rule.info.ruleTrace

        val subJoins = buildJoinRule(rule, trace.stepTrace(Step.BUILD))
            ?: return null

        val a2trTrace = trace.stepTrace(Step.AUTOMATA_TO_TAINT_RULE)
        val strategy = strategyFor(rule.info) ?: return null
        return runCatching {
            val rules = convertJoinRuleWithStrategy(strategy, rule, subJoins, a2trTrace)
                ?: return null
            rules to rule.info.metadata
        }.onFailure { ex ->
            a2trTrace.error(FailedToCreateTaintRules(ex.message))
            return null
        }.getOrThrow().also {
            trace.info("Generate ${it.first.size} rules from ${it.first.ruleId}")
        }
    }

    /**
     * Converts each single-sink [TaintAutomataJoinRule] produced by [buildJoinRule] and merges the
     * results into one rule. When a join fans into several sinks each sink is renamed apart (its key is
     * appended to the rule id) so the generated marks of one sink cannot collide with another's; the
     * merged rule is still published under the original rule id.
     */
    private fun <P : Any, R> convertJoinRuleWithStrategy(
        strategy: LanguageStrategy<P, R>,
        rule: JoinRule<*>,
        subJoins: List<Pair<String, TaintAutomataJoinRule>>,
        trace: SemgrepRuleLoadStepTrace,
    ): TaintRuleFromSemgrep<R>? {
        val typeOps = strategy.typeOps
        val renameSinks = subJoins.size > 1
        val groups = mutableListOf<TaintRuleFromSemgrep.TaintRuleGroup<R>>()
        for ((sinkKey, subRule) in subJoins) {
            val ruleId = if (renameSinks) "${rule.info.ruleId}#$sinkKey" else rule.info.ruleId
            val ctx = RuleConversionCtx(ruleId, rule.modeModifier(), rule.info.sinkMeta, trace, typeOps)
            val converted = ctx.convertTaintAutomataJoinToTaintRules(strategy.taintRuleStrategy, subRule)
                ?: return null
            groups += converted.taintRules
        }
        return TaintRuleFromSemgrep(rule.info.ruleId, groups)
    }

    private fun resolveBuiltRuleWrtOverrides(
        ruleId: String,
        trace: SemgrepRuleLoadStepTrace,
        overrideChain: MutableSet<String>
    ): NormalRule<BuiltRule>? {
        val parsedRule = parsedRules[ruleId]
        if (parsedRule == null) {
            trace.error(RefRuleNotRegistered(ruleId))
            return null
        }

        if (parsedRule is RuleOverride<*>) {
            if (!overrideChain.add(ruleId)) {
                trace.error(OverrideLoop())
                return null
            }

            return resolveBuiltRuleWrtOverrides(parsedRule.refId, trace, overrideChain)
        }

        val builtRule = builtNormalRules[ruleId]
        if (builtRule == null) {
            trace.error(RefRuleNotLoaded(ruleId))
            return null
        }

        return builtRule
    }

    private fun buildJoinRule(
        rule: JoinRule<*>,
        trace: SemgrepRuleLoadStepTrace
    ): List<Pair<String, TaintAutomataJoinRule>>? {
        val items = hashMapOf<String, MutableList<TaintAutomataJoinRuleItem>>()
        val itemRenames = hashMapOf<String, List<Pair<MetavarAtom, MetavarAtom>>>()

        val strategy = strategyFor(rule.info) ?: return null

        for (ref in rule.refs) {
            if (ref.`as` in items) {
                trace.error(JoinRefDuplicateAlias(ref.`as`))
                return null
            }

            val refIds = resolveRefTargets(ref, rule.info.pathInfo.ruleRelativePath, trace)
                ?: return null

            val renames = ref.renames.map {
                val from = strategy.parseMetaVar(it.from, trace) ?: return null
                val to = strategy.parseMetaVar(it.to, trace) ?: return null
                Pair(from, to)
            }

            val aliasItems = items.getOrPut(ref.`as`, ::mutableListOf)
            for (refId in refIds) {
                if (parsedRules[refId] is JoinRule<*>) {
                    trace.error(JoinRefToUnsupportedRuleKind(refId))
                    return null
                }
                val itemAutomata = resolveBuiltRuleWrtOverrides(refId, trace, hashSetOf())
                    ?: return null
                aliasItems += TaintAutomataJoinRuleItem(itemAutomata.info.ruleId, itemAutomata.rule)
            }
            itemRenames[ref.`as`] = renames
        }

        val operations = rule.on.map { op ->
            if (op.left.ruleName !in items || op.right.ruleName !in items) {
                trace.error(IncorrectJoinOnCondition())
                return null
            }

            val lhs = strategy.parseJoinMetaVarWithRenames(op.left, itemRenames, trace) ?: return null
            val rhs = strategy.parseJoinMetaVarWithRenames(op.right, itemRenames, trace) ?: return null

            TaintAutomataJoinOperation(op.op, lhs, rhs)
        }

        if (operations.isEmpty()) {
            trace.error(JoinRuleWithoutJoinOn())
            return null
        }

        return expandToSingleSinkJoins(items, operations, trace)
    }

    /**
     * Lowers a (possibly tag-expanded, possibly multi-sink) alias-level join onto the single-sink join
     * form the conversion engine accepts. A source alias that resolves to several rules contributes one
     * item per rule; every distinct sink becomes its own [TaintAutomataJoinRule] wiring that sink's
     * source union into it. The returned pairs carry a per-sink key used to rename the sinks apart during
     * conversion. Chained aliases (an alias used as both a source and a sink) and aliases referenced with
     * conflicting metavariables are rejected here, because per-sink splitting would otherwise hide them.
     */
    private fun expandToSingleSinkJoins(
        items: Map<String, List<TaintAutomataJoinRuleItem>>,
        operations: List<TaintAutomataJoinOperation>,
        trace: SemgrepRuleLoadStepTrace
    ): List<Pair<String, TaintAutomataJoinRule>>? {
        val sourceAliases = operations.mapTo(linkedSetOf()) { it.lhs.itemId }
        val sinkAliases = operations.mapTo(linkedSetOf()) { it.rhs.itemId }
        if (sourceAliases.intersect(sinkAliases).isNotEmpty()) {
            trace.error(JoinRuleWithChainedOperations())
            return null
        }

        val sourceVar = hashMapOf<String, MetavarAtom>()
        val sinkVar = hashMapOf<String, MetavarAtom>()
        for (op in operations) {
            val prevSource = sourceVar.put(op.lhs.itemId, op.lhs.metaVar)
            if (prevSource != null && prevSource != op.lhs.metaVar) {
                trace.error(JoinAliasMetavarConflict(op.lhs.itemId))
                return null
            }
            val prevSink = sinkVar.put(op.rhs.itemId, op.rhs.metaVar)
            if (prevSink != null && prevSink != op.rhs.metaVar) {
                trace.error(JoinAliasMetavarConflict(op.rhs.itemId))
                return null
            }
        }

        // Keep a single-rule alias' item id equal to the alias so common joins convert exactly as before;
        // only tag-expanded aliases (more than one rule) get an index suffix.
        fun itemId(alias: String, index: Int, count: Int): String =
            if (count == 1) alias else "$alias#$index"

        val subJoins = mutableListOf<Pair<String, TaintAutomataJoinRule>>()
        for (sinkAlias in sinkAliases) {
            val opsForSink = operations.filter { it.rhs.itemId == sinkAlias }
            val sinkItems = items.getValue(sinkAlias)

            sinkItems.forEachIndexed { sinkIdx, sinkItem ->
                val sinkItemId = itemId(sinkAlias, sinkIdx, sinkItems.size)
                val sinkRef = TaintAutomataJoinMetaVarRef(sinkItemId, sinkVar.getValue(sinkAlias))
                val subItems = linkedMapOf(sinkItemId to sinkItem)
                val subOps = linkedSetOf<TaintAutomataJoinOperation>()

                for (op in opsForSink) {
                    val sourceItems = items.getValue(op.lhs.itemId)
                    sourceItems.forEachIndexed { sourceIdx, sourceItem ->
                        val sourceItemId = itemId(op.lhs.itemId, sourceIdx, sourceItems.size)
                        subItems[sourceItemId] = sourceItem
                        subOps += TaintAutomataJoinOperation(
                            op.op,
                            TaintAutomataJoinMetaVarRef(sourceItemId, op.lhs.metaVar),
                            sinkRef
                        )
                    }
                }

                subJoins += sinkItemId to TaintAutomataJoinRule(subItems, subOps.toList())
            }
        }

        return subJoins
    }

    private fun resolveRefTargets(
        ref: SemgrepYamlJoinRuleRef,
        ruleRelativePath: Path,
        trace: SemgrepRuleLoadStepTrace
    ): List<String>? {
        val hasRule = ref.rule != null
        val hasTag = ref.tag != null
        if (hasRule == hasTag) {
            trace.error(if (hasRule) JoinRefAmbiguousTarget() else JoinRefMissingTarget())
            return null
        }

        if (hasRule) {
            return listOf(resolveRefRuleId(ref.rule!!, ruleRelativePath))
        }

        val matched = tagIndex[ref.tag]
        if (matched.isNullOrEmpty()) {
            trace.error(EmptyTagExpansion(ref.tag!!))
            return null
        }
        return matched.distinct().sorted()
    }

    private fun LanguageStrategy<*, *>.parseJoinMetaVarWithRenames(
        ref: SemgrepJoinRuleOnVar,
        renames: Map<String, List<Pair<MetavarAtom, MetavarAtom>>>,
        trace: SemgrepRuleLoadStepTrace
    ): TaintAutomataJoinMetaVarRef? {
        var metaVar = parseMetaVar(ref.varName, trace) ?: return null
        val rename = renames[ref.ruleName].orEmpty()

        for ((from, to) in rename) {
            if (to == metaVar) {
                metaVar = from
            }
        }

        return TaintAutomataJoinMetaVarRef(ref.ruleName, metaVar)
    }

    private fun parseRuleInfo(rule: RegisteredRule, forceLibraryMode: Boolean): RuleInfo {
        val semgrepRule = rule.rule
        val ruleCwe = semgrepRule.cweInfo()
        val severity = when (semgrepRule.severity.lowercase()) {
            "high", "critical", "error" -> Severity.Error
            "medium", "warning" -> Severity.Warning
            else -> Severity.Note
        }

        val sinkMeta = SinkMetaData(ruleCwe, semgrepRule.message, severity)
        val metadata = RuleMetadata(rule.ruleId, semgrepRule.id, semgrepRule.message, severity, semgrepRule.metadata)
        val overrides = semgrepRule.overrides(rule.pathInfo.ruleRelativePath)
        val language = strategyFor(semgrepRule)?.language
        val primitiveTracking = semgrepRule.primitiveTrackingEnabled()
        return RuleInfo(
            rule.ruleId, semgrepRule.id,
            language = language,
            primitiveTracking = primitiveTracking,
            overridesRuleId = overrides,
            isLibraryRule = forceLibraryMode || semgrepRule.isLibraryRule(),
            isDisabled = semgrepRule.isDisabled(),
            metadata, sinkMeta, rule.ruleTrace, rule.pathInfo
        )
    }

    private fun SemgrepYamlRule.isSupportedRule(): Boolean = strategyFor(this) != null

    private fun SemgrepYamlRule.isLibraryRule(): Boolean =
        options?.getBoolKeyOrFalse("lib") ?: false

    private fun SemgrepYamlRule.isDisabled(): Boolean =
        options?.getKey("disabled") != null

    private fun SemgrepYamlRule.overrides(ruleRelativePath: Path): String? {
        val overrides = options?.getScalar("overrides") ?: return null
        return resolveRefRuleId(overrides.content, ruleRelativePath)
    }

    private fun SemgrepYamlRule.primitiveTrackingEnabled(): Boolean =
        options?.getBoolKeyOrFalse("primitive-tracking") ?: false

    private fun SemgrepYamlRule.cweInfo(): List<Int>? {
        val rawCwes = metadata?.readStrings("cwe") ?: return null
        val cwes = rawCwes.mapNotNull { s -> parseCwe(s) }
        return cwes.ifEmpty { null }
    }

    private fun parseCwe(str: String): Int? {
        val match = cweRegex.matchEntire(str) ?: return null
        return match.groupValues[1].toInt()
    }

    private fun RuleSetPathInfo.ruleSetName(): String = ruleRelativePath.ruleSetName()
    private fun Path.ruleSetName(): String = this.toString()

    private fun resolveRefRuleId(refRule: String, ruleRelativePath: Path): String {
        val refRuleId = refRule.substringAfter('#')

        val refRulePath = refRule.substringBefore('#', missingDelimiterValue = "")
            .takeIf { it.isNotBlank() }
            ?.removePrefix("/")
            ?.let { Path(it) }

        val refRulePathInfo = refRulePath ?: ruleRelativePath
        val refRuleSetName = refRulePathInfo.ruleSetName()
        return SemgrepRuleUtils.getRuleId(refRuleSetName, refRuleId)
    }

    private fun ruleSeverityAllow(rule: Rule<*>, severity: List<Severity>): Boolean =
        severity.isEmpty() || severity.contains(rule.info.metadata.severity)

    private fun ruleIdAllow(rule: Rule<*>, ruleIdFilter: List<String>): Boolean =
        ruleIdFilter.isEmpty() || rule.info.ruleId in ruleIdFilter

    private fun Rule<*>.modeModifier(): String? {
        if (!info.primitiveTracking) return null
        return PrimitiveTaintExt.PRIMITIVE_TRACKING_ENABLED_MODE
    }

    companion object {
        private val cweRegex = Regex("CWE-(\\d+).*", RegexOption.IGNORE_CASE)
    }
}
