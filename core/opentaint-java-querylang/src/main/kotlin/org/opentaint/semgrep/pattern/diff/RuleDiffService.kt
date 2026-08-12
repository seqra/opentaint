package org.opentaint.semgrep.pattern.diff

import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.conversion.LanguageStrategy
import org.opentaint.semgrep.pattern.diff.automata.TaintAutomataComparator
import org.opentaint.semgrep.pattern.diff.load.ParsedJoinRuleSnapshot
import org.opentaint.semgrep.pattern.diff.load.ParsedNormalRuleSnapshot
import org.opentaint.semgrep.pattern.diff.load.ParsedRuleDescriptor
import org.opentaint.semgrep.pattern.diff.load.ResolvedJoinRuleSnapshot
import org.opentaint.semgrep.pattern.diff.load.RuleDiffLoadCollector
import java.nio.file.Path
import kotlin.io.path.Path
import kotlin.io.path.extension
import kotlin.io.path.isDirectory
import kotlin.io.path.name
import kotlin.io.path.readText
import kotlin.io.path.relativeTo
import kotlin.io.path.walk

data class RuleFileInput(
    val relativePath: Path,
    val text: String,
)

/** A complete rule universe and the rule in that universe to compare. */
data class RuleInput(
    val files: List<RuleFileInput>,
    /** Internal qualified id (`path.yaml:id`) or an unambiguous short id. */
    val ruleId: String,
    val rulesRoot: Path = Path("."),
) {
    companion object {
        /** Reads one YAML file or a complete, recursively discovered YAML rule universe. */
        fun fromPath(path: Path, ruleId: String): RuleInput {
            if (!path.isDirectory()) {
                val root = path.parent ?: path.toAbsolutePath().parent
                return RuleInput(
                    files = listOf(RuleFileInput(Path(path.name), path.readText())),
                    ruleId = ruleId,
                    rulesRoot = root,
                )
            }
            val files = path.walk()
                .filter { !it.isDirectory() && it.extension.lowercase() in setOf("yaml", "yml") }
                .sortedBy { it.toString() }
                .map { RuleFileInput(it.relativeTo(path), it.readText()) }
                .toList()
            return RuleInput(files, ruleId, path)
        }
    }
}

data class RuleDiffOptions(
    val compareMetadata: Boolean = true,
)

/**
 * Public rule-diff entry point. Each input is fully loaded by an independent loader before any
 * structural or automata comparison begins.
 */
class RuleDiffService(
    private val strategies: List<LanguageStrategy<*, *>>,
    private val automataComparator: TaintAutomataComparator = TaintAutomataComparator(),
) {
    fun comparePaths(
        oldPath: Path,
        newPath: Path,
        oldRuleId: String,
        newRuleId: String = oldRuleId,
        options: RuleDiffOptions = RuleDiffOptions(),
    ): RuleDiffResult = compare(
        RuleInput.fromPath(oldPath, oldRuleId),
        RuleInput.fromPath(newPath, newRuleId),
        options,
    )

    fun compare(
        old: RuleInput,
        new: RuleInput,
        options: RuleDiffOptions = RuleDiffOptions(),
    ): RuleDiffResult {
        val oldLoaded = load(old)
        val newLoaded = load(new)
        val oldSelected = oldLoaded.select(old.ruleId)
        val newSelected = newLoaded.select(new.ruleId)

        val selectionError = oldLoaded.failure?.let { "Old rule universe failed to load: $it" }
            ?: newLoaded.failure?.let { "New rule universe failed to load: $it" }
            ?: oldSelected.error?.let { "Old rule: $it" }
            ?: newSelected.error?.let { "New rule: $it" }
        if (selectionError != null) {
            return loadFailed(oldLoaded, newLoaded, oldSelected.descriptor, newSelected.descriptor, selectionError)
        }
        if (!oldSelected.wasFullyLoaded || !newSelected.wasFullyLoaded) {
            val sides = buildList {
                if (!oldSelected.wasFullyLoaded) add("old")
                if (!newSelected.wasFullyLoaded) add("new")
            }.joinToString(" and ")
            return loadFailed(
                oldLoaded,
                newLoaded,
                oldSelected.descriptor,
                newSelected.descriptor,
                "Selected $sides rule did not complete normal loading",
            )
        }

        val oldLanguage = oldSelected.descriptor!!.language
        val newLanguage = newSelected.descriptor!!.language
        if (oldLanguage != newLanguage) {
            return loadFailed(
                oldLoaded, newLoaded, oldSelected.descriptor, newSelected.descriptor,
                "Cannot compare different languages: old=$oldLanguage, new=$newLanguage",
            )
        }
        val strategy = strategies.firstOrNull { it.language == oldLanguage }
            ?: return loadFailed(
                oldLoaded, newLoaded, oldSelected.descriptor, newSelected.descriptor,
                "No language strategy for $oldLanguage",
            )

        val accumulator = ComparisonAccumulator()
        when {
            oldSelected.normal != null && newSelected.normal != null -> {
                accumulator.add(
                    NormalRuleDiffEngine(strategy, automataComparator, options.compareMetadata)
                        .compare(oldSelected.normal, newSelected.normal)
                )
            }
            oldSelected.join != null && newSelected.join != null -> {
                compareJoins(
                    oldLoaded, newLoaded, oldSelected.join, newSelected.join,
                    strategy, options.compareMetadata, accumulator,
                )
            }
            else -> accumulator.structureChanges += StructureChange(
                StructureChangeKind.RULE_MODE_CHANGED,
                "Rule mode changed from ${oldSelected.kind} to ${newSelected.kind}",
            )
        }

        if (options.compareMetadata &&
            oldSelected.metadataKey != newSelected.metadataKey &&
            accumulator.structureChanges.none { it.kind == StructureChangeKind.RULE_METADATA_CHANGED }
        ) {
            accumulator.structureChanges += StructureChange(
                StructureChangeKind.RULE_METADATA_CHANGED,
                "Rule metadata changed",
            )
        }

        val hasChanges = accumulator.structureChanges.isNotEmpty() ||
            accumulator.added.isNotEmpty() || accumulator.removed.isNotEmpty() ||
            accumulator.automataMatches.any { !it.equivalent }
        val complete = accumulator.inconclusive.isEmpty()
        val status = when {
            hasChanges -> RuleDiffStatus.CHANGED
            !complete -> RuleDiffStatus.INCONCLUSIVE
            else -> RuleDiffStatus.EQUIVALENT
        }
        return RuleDiffResult(
            status = status,
            comparisonComplete = complete,
            hasProvenChanges = hasChanges,
            oldRule = oldSelected.descriptor,
            newRule = newSelected.descriptor,
            oldLoadTrace = oldLoaded.trace,
            newLoadTrace = newLoaded.trace,
            structureChanges = accumulator.structureChanges.distinct()
                .sortedWith(compareBy({ it.kind.ordinal }, { it.detail })),
            exactCubeMatches = accumulator.exact.map {
                CubeReference.from(it.old) to CubeReference.from(it.new)
            },
            automataCubeMatches = accumulator.automataMatches,
            addedCubes = accumulator.added.map(CubeReference::from),
            removedCubes = accumulator.removed.map(CubeReference::from),
            traceSamples = accumulator.automataMatches.flatMap { it.witnesses }
                .plus(accumulator.directionalTraceSamples)
                .distinctBy { Triple(it.direction, it.observation, it.steps) },
            inconclusiveComparisons = accumulator.inconclusive.distinct(),
        )
    }

    private fun compareJoins(
        oldLoaded: LoadedUniverse,
        newLoaded: LoadedUniverse,
        old: ParsedJoinRuleSnapshot,
        new: ParsedJoinRuleSnapshot,
        strategy: LanguageStrategy<*, *>,
        compareMetadata: Boolean,
        accumulator: ComparisonAccumulator,
    ) {
        multisetDiff(old.refs.map(::joinRefKey), new.refs.map(::joinRefKey)).let { (removed, added) ->
            removed.forEach { accumulator.structureChanges += StructureChange(StructureChangeKind.JOIN_REF_REMOVED, it) }
            added.forEach { accumulator.structureChanges += StructureChange(StructureChangeKind.JOIN_REF_ADDED, it) }
        }
        multisetDiff(old.operations.map(::joinOperationKey), new.operations.map(::joinOperationKey)).let { (removed, added) ->
            removed.forEach {
                accumulator.structureChanges += StructureChange(StructureChangeKind.JOIN_OPERATION_REMOVED, it)
            }
            added.forEach {
                accumulator.structureChanges += StructureChange(StructureChangeKind.JOIN_OPERATION_ADDED, it)
            }
        }

        val oldResolved = oldLoaded.collector.resolvedJoinRules[old.descriptor.qualifiedRuleId]
        val newResolved = newLoaded.collector.resolvedJoinRules[new.descriptor.qualifiedRuleId]
        if (oldResolved == null || newResolved == null) {
            accumulator.inconclusive += InconclusiveCubeComparison(
                null, null, "Resolved join snapshot is unavailable",
            )
            return
        }
        compareResolvedJoinStructure(oldResolved, newResolved, accumulator)

        // Target overlap establishes operand identity before aliases are compared structurally.
        // This keeps an alias rename from hiding changes inside the referenced rule.
        val remainingNewItems = newResolved.items.values.sortedBy { it.itemId }.toMutableList()
        oldResolved.items.values.sortedBy { it.itemId }.forEach { oldItem ->
            val candidate = remainingNewItems.withIndex().minWithOrNull(
                compareBy<IndexedValue<org.opentaint.semgrep.pattern.diff.load.ResolvedJoinItemSnapshot>>(
                    { it.value.effectiveRuleId.shortRuleId() != oldItem.effectiveRuleId.shortRuleId() },
                    { it.value.referencedRuleId.shortRuleId() != oldItem.referencedRuleId.shortRuleId() },
                    { it.value.alias != oldItem.alias },
                    { it.value.itemId },
                )
            ) ?: return@forEach
            val newItem = remainingNewItems.removeAt(candidate.index)
            run {
                val oldNormal = oldLoaded.effectiveNormal(oldItem.effectiveRuleId)
                val newNormal = newLoaded.effectiveNormal(newItem.effectiveRuleId)
                if (oldNormal == null || newNormal == null) {
                    accumulator.inconclusive += InconclusiveCubeComparison(
                        null, null,
                        "Join operand ${oldItem.alias}/${newItem.alias} could not be mapped to a parsed normal rule",
                    )
                } else {
                    accumulator.add(
                        NormalRuleDiffEngine(strategy, automataComparator, compareMetadata)
                            .compare(oldNormal, newNormal)
                    )
                }
            }
        }
    }

    private fun compareResolvedJoinStructure(
        old: ResolvedJoinRuleSnapshot,
        new: ResolvedJoinRuleSnapshot,
        accumulator: ComparisonAccumulator,
    ) {
        val oldItems = old.items.values.map {
            "${it.alias}:${it.referencedRuleId.shortRuleId()}->${it.effectiveRuleId.shortRuleId()}"
        }
        val newItems = new.items.values.map {
            "${it.alias}:${it.referencedRuleId.shortRuleId()}->${it.effectiveRuleId.shortRuleId()}"
        }
        val (removedItems, addedItems) = multisetDiff(oldItems, newItems)
        (removedItems.map { "removed $it" } + addedItems.map { "added $it" }).forEach {
            accumulator.structureChanges += StructureChange(StructureChangeKind.JOIN_RESOLUTION_CHANGED, it)
        }

        val (removedOps, addedOps) = multisetDiff(
            old.operations.map { it.toString() },
            new.operations.map { it.toString() },
        )
        if (removedOps.isNotEmpty() || addedOps.isNotEmpty()) {
            accumulator.structureChanges += StructureChange(
                StructureChangeKind.JOIN_RESOLUTION_CHANGED,
                "Resolved operations changed: removed=$removedOps, added=$addedOps",
            )
        }
    }

    private fun load(input: RuleInput): LoadedUniverse {
        val trace = SemgrepLoadTrace()
        val collector = RuleDiffLoadCollector()
        val loader = SemgrepRuleLoader(strategies, listOf(collector))
        var failure: String? = null
        val result = runCatching {
            input.files.sortedBy { it.relativePath.toString() }.forEach { file ->
                loader.registerRuleSet(file.text, file.relativePath, input.rulesRoot, trace)
            }
            loader.loadRules()
        }.getOrElse { error ->
            failure = error.message ?: error::class.simpleName ?: "unknown load failure"
            SemgrepRuleLoader.RuleLoadResult(emptyList(), emptySet())
        }
        return LoadedUniverse(collector, result, trace, failure)
    }

    private fun loadFailed(
        old: LoadedUniverse,
        new: LoadedUniverse,
        oldDescriptor: ParsedRuleDescriptor?,
        newDescriptor: ParsedRuleDescriptor?,
        message: String,
    ) = RuleDiffResult(
        status = RuleDiffStatus.LOAD_FAILED,
        comparisonComplete = false,
        hasProvenChanges = false,
        oldRule = oldDescriptor,
        newRule = newDescriptor,
        oldLoadTrace = old.trace,
        newLoadTrace = new.trace,
        loadFailure = message,
    )

    private data class LoadedUniverse(
        val collector: RuleDiffLoadCollector,
        val result: SemgrepRuleLoader.RuleLoadResult,
        val trace: SemgrepLoadTrace,
        val failure: String?,
    ) {
        fun select(ruleId: String): SelectedRule {
            val normals = collector.normalRules.values.filter { it.matches(ruleId) }
            val joins = collector.joinRules.values.filter { it.descriptor.matches(ruleId) }
            val all = normals.map { SelectedRule(normal = it) } + joins.map { SelectedRule(join = it) }
            if (all.isEmpty()) return SelectedRule(error = "Rule '$ruleId' was not parsed")
            if (all.size != 1) return SelectedRule(error = "Rule '$ruleId' is ambiguous (${all.size} matches)")
            val selected = all.single()
            val loadedIds = result.rulesWithMeta.mapTo(hashSetOf()) { it.first.ruleId }
            return selected.copy(wasFullyLoaded = selected.descriptor?.qualifiedRuleId in loadedIds)
        }

        fun effectiveNormal(ruleId: String): ParsedNormalRuleSnapshot? {
            collector.normalRules[ruleId]?.let { return it }
            val override = collector.overrides[ruleId] ?: return null
            return override.effectiveRuleId?.let(collector.normalRules::get)
        }
    }

    private data class SelectedRule(
        val normal: ParsedNormalRuleSnapshot? = null,
        val join: ParsedJoinRuleSnapshot? = null,
        val error: String? = null,
        val wasFullyLoaded: Boolean = false,
    ) {
        val descriptor: ParsedRuleDescriptor? get() = normal?.descriptor ?: join?.descriptor
        val kind: String get() = if (normal != null) "normal" else if (join != null) "join" else "missing"
        val metadataKey: Any? get() = (normal?.metadata ?: join?.metadata)?.let {
            listOf(it.shortRuleId, it.message, it.severity, it.metadata)
        }
    }

    private class ComparisonAccumulator {
        val structureChanges = mutableListOf<StructureChange>()
        val exact = mutableListOf<CubeMatch>()
        val automataMatches = mutableListOf<AutomataCubeMatch>()
        val added = mutableListOf<ContextualCube>()
        val removed = mutableListOf<ContextualCube>()
        val inconclusive = mutableListOf<InconclusiveCubeComparison>()
        val directionalTraceSamples = mutableListOf<org.opentaint.semgrep.pattern.diff.automata.AutomataTraceWitness>()

        fun add(comparison: NormalRuleComparison) {
            structureChanges += comparison.structureChanges
            exact += comparison.exactMatches
            automataMatches += comparison.automataMatches
            added += comparison.added
            removed += comparison.removed
            inconclusive += comparison.inconclusive
            directionalTraceSamples += comparison.directionalTraceSamples
        }
    }
}

private fun ParsedNormalRuleSnapshot.matches(ruleId: String): Boolean = descriptor.matches(ruleId)

private fun ParsedRuleDescriptor.matches(ruleId: String): Boolean =
    qualifiedRuleId == ruleId || shortRuleId == ruleId

private fun joinRefKey(ref: org.opentaint.semgrep.pattern.SemgrepYamlJoinRuleRef): String =
    "selector=${ref.rule?.let { "rule:$it" } ?: "tag:${ref.tag}"},alias=${ref.`as`},renames=${ref.renames.sortedBy { it.from }.joinToString()}"

private fun joinOperationKey(operation: org.opentaint.semgrep.pattern.SemgrepJoinRuleOn): String =
    "${operation.left.ruleName}.${operation.left.varName}${operation.op.op}${operation.right.ruleName}.${operation.right.varName}"

private fun multisetDiff(old: List<String>, new: List<String>): Pair<List<String>, List<String>> {
    val remainingNew = new.toMutableList()
    val removed = mutableListOf<String>()
    old.sorted().forEach { value ->
        val index = remainingNew.indexOf(value)
        if (index < 0) removed += value else remainingNew.removeAt(index)
    }
    return removed to remainingNew.sorted()
}

private fun String.shortRuleId(): String = substringAfterLast('#').substringAfterLast(':')
