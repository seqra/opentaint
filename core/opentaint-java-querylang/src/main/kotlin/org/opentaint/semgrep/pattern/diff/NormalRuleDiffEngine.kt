package org.opentaint.semgrep.pattern.diff

import org.opentaint.semgrep.pattern.Formula
import org.opentaint.semgrep.pattern.SemgrepMatchingRule
import org.opentaint.semgrep.pattern.SemgrepRuleLoadTrace
import org.opentaint.semgrep.pattern.SemgrepTaintRule
import org.opentaint.semgrep.pattern.SemgrepTraceEntry.Step
import org.opentaint.semgrep.pattern.conversion.LanguageStrategy
import org.opentaint.semgrep.pattern.diff.automata.TaintAutomataComparator
import org.opentaint.semgrep.pattern.diff.automata.TaintAutomataComparison
import org.opentaint.semgrep.pattern.diff.load.ParsedNormalRuleSnapshot
import org.opentaint.semgrep.pattern.diff.structure.formulaToDnfCubes

internal data class NormalRuleComparison(
    val structureChanges: List<StructureChange>,
    val exactMatches: List<CubeMatch>,
    val automataMatches: List<AutomataCubeMatch>,
    val added: List<ContextualCube>,
    val removed: List<ContextualCube>,
    val inconclusive: List<InconclusiveCubeComparison>,
    val directionalTraceSamples: List<org.opentaint.semgrep.pattern.diff.automata.AutomataTraceWitness>,
)

internal class NormalRuleDiffEngine(
    private val strategy: LanguageStrategy<*, *>,
    private val comparator: TaintAutomataComparator,
    private val compareMetadata: Boolean = true,
) {
    private val compilationCache = mutableMapOf<ContextualCube, Result<CompiledCube>>()

    fun compare(
        old: ParsedNormalRuleSnapshot,
        new: ParsedNormalRuleSnapshot,
    ): NormalRuleComparison {
        val oldCubes = extractCubes(old)
        val newCubes = extractCubes(new)
        val plan = ExactCubeMatcher.match(oldCubes, newCubes)
        val pairing = pairUnmatched(plan.unmatchedOld, plan.unmatchedNew, old, new)
        val directionalSamples = sampleAddedAndRemoved(pairing.added, pairing.removed, old, new)
        val mapped = plan.exactMatches + pairing.matches
        val changes = structuralChanges(old, new, mapped, pairing.added, pairing.removed).toMutableList()
        pairing.inconclusive.filter { it.oldCube != null && it.newCube != null }.forEach {
            changes += StructureChange(
                StructureChangeKind.CUBE_EXPRESSION_CHANGED,
                "Cube expression changed; automata comparison was inconclusive",
                it.oldCube,
                it.newCube,
            )
        }

        return NormalRuleComparison(
            structureChanges = changes,
            exactMatches = plan.exactMatches,
            automataMatches = pairing.reports,
            added = pairing.added,
            removed = pairing.removed,
            inconclusive = pairing.inconclusive + directionalSamples.inconclusive,
            directionalTraceSamples = directionalSamples.witnesses,
        )
    }

    private data class DirectionalSamples(
        val witnesses: List<org.opentaint.semgrep.pattern.diff.automata.AutomataTraceWitness>,
        val inconclusive: List<InconclusiveCubeComparison>,
    )

    private fun sampleAddedAndRemoved(
        added: List<ContextualCube>,
        removed: List<ContextualCube>,
        oldRule: ParsedNormalRuleSnapshot,
        newRule: ParsedNormalRuleSnapshot,
    ): DirectionalSamples {
        val samples = mutableListOf<org.opentaint.semgrep.pattern.diff.automata.AutomataTraceWitness>()
        val inconclusive = mutableListOf<InconclusiveCubeComparison>()
        fun sample(
            cube: ContextualCube,
            rule: ParsedNormalRuleSnapshot,
            direction: org.opentaint.semgrep.pattern.diff.automata.AutomataTraceDirection,
        ) {
            val compiled = compileCube(cube, rule)
            if (compiled.isFailure) {
                inconclusive += InconclusiveCubeComparison(
                    CubeReference.from(cube).takeIf {
                        direction == org.opentaint.semgrep.pattern.diff.automata.AutomataTraceDirection.OLD_ONLY
                    },
                    CubeReference.from(cube).takeIf {
                        direction == org.opentaint.semgrep.pattern.diff.automata.AutomataTraceDirection.NEW_ONLY
                    },
                    "CUBE_COMPILATION_FAILED: ${compiled.exceptionOrNull()?.message}",
                )
                return
            }
            if (compiled.getOrThrow().variants.isEmpty()) {
                inconclusive += InconclusiveCubeComparison(
                    CubeReference.from(cube).takeIf {
                        direction == org.opentaint.semgrep.pattern.diff.automata.AutomataTraceDirection.OLD_ONLY
                    },
                    CubeReference.from(cube).takeIf {
                        direction == org.opentaint.semgrep.pattern.diff.automata.AutomataTraceDirection.NEW_ONLY
                    },
                    "Cube compilation produced no automata variants",
                )
                return
            }
            compiled.getOrThrow().variants.mapNotNullTo(samples) {
                comparator.sampleAgainstEmpty(it, direction)
            }
        }
        removed.forEach { cube ->
            sample(
                cube,
                oldRule,
                org.opentaint.semgrep.pattern.diff.automata.AutomataTraceDirection.OLD_ONLY,
            )
        }
        added.forEach { cube ->
            sample(
                cube,
                newRule,
                org.opentaint.semgrep.pattern.diff.automata.AutomataTraceDirection.NEW_ONLY,
            )
        }
        return DirectionalSamples(
            samples.distinctBy { Triple(it.direction, it.observation, it.steps) },
            inconclusive,
        )
    }

    private fun extractCubes(snapshot: ParsedNormalRuleSnapshot): List<ContextualCube> {
        val trace = SemgrepRuleLoadTrace(
            snapshot.descriptor.qualifiedRuleId,
            snapshot.descriptor.shortRuleId,
        ).stepTrace(Step.BUILD_CONVERT_TO_RAW_RULE)
        val owner = snapshot.descriptor.qualifiedRuleId
        val result = mutableListOf<ContextualCube>()

        fun add(kind: RulePartKind, ordinal: Int, formula: Formula, context: CubeContext) {
            formulaToDnfCubes(formula, trace).forEach { cube ->
                result += ContextualCube(owner, kind, ordinal, cube, context)
            }
        }

        when (val rule = snapshot.rule) {
            is SemgrepMatchingRule -> rule.rules.forEachIndexed { index, formula ->
                add(RulePartKind.MATCHING, index, formula, CubeContext.Matching)
            }
            is SemgrepTaintRule -> {
                rule.sources.forEachIndexed { index, declaration ->
                    add(RulePartKind.SOURCE, index, declaration.pattern, CubeContext.Source(declaration))
                }
                rule.sinks.forEachIndexed { index, declaration ->
                    add(RulePartKind.SINK, index, declaration.pattern, CubeContext.Sink(declaration))
                }
                rule.propagators.forEachIndexed { index, declaration ->
                    add(RulePartKind.PROPAGATOR, index, declaration.pattern, CubeContext.Propagator(declaration))
                }
                rule.sanitizers.forEachIndexed { index, declaration ->
                    add(RulePartKind.SANITIZER, index, declaration.pattern, CubeContext.Sanitizer(declaration))
                }
            }
        }
        return result
    }

    private data class UnmatchedPairing(
        val matches: List<CubeMatch>,
        val reports: List<AutomataCubeMatch>,
        val added: List<ContextualCube>,
        val removed: List<ContextualCube>,
        val inconclusive: List<InconclusiveCubeComparison>,
    )

    private data class Candidate(
        val old: ContextualCube,
        val new: ContextualCube,
        val comparison: TaintAutomataComparison,
    )

    private fun pairUnmatched(
        oldCubes: List<ContextualCube>,
        newCubes: List<ContextualCube>,
        oldRule: ParsedNormalRuleSnapshot,
        newRule: ParsedNormalRuleSnapshot,
    ): UnmatchedPairing {
        if (oldCubes.isEmpty() || newCubes.isEmpty()) {
            return UnmatchedPairing(emptyList(), emptyList(), newCubes, oldCubes, emptyList())
        }

        val oldCompiled = oldCubes.associateWith { cube ->
            compileCube(cube, oldRule)
        }
        val newCompiled = newCubes.associateWith { cube ->
            compileCube(cube, newRule)
        }
        val candidates = mutableListOf<Candidate>()
        val inconclusive = mutableListOf<InconclusiveCubeComparison>()

        for (oldCube in oldCubes) for (newCube in newCubes) {
            val oldResult = oldCompiled.getValue(oldCube)
            val newResult = newCompiled.getValue(newCube)
            val comparison = when {
                oldResult.isFailure -> TaintAutomataComparison.Inconclusive(
                    org.opentaint.semgrep.pattern.diff.automata.AutomataInconclusiveReason.CUBE_COMPILATION_FAILED,
                    "Old cube compilation failed: ${oldResult.exceptionOrNull()?.message}",
                )
                newResult.isFailure -> TaintAutomataComparison.Inconclusive(
                    org.opentaint.semgrep.pattern.diff.automata.AutomataInconclusiveReason.CUBE_COMPILATION_FAILED,
                    "New cube compilation failed: ${newResult.exceptionOrNull()?.message}",
                )
                else -> compareVariants(oldResult.getOrThrow().variants, newResult.getOrThrow().variants)
            }
            candidates += Candidate(oldCube, newCube, comparison)
        }

        val remainingOld = oldCubes.toMutableSet()
        val remainingNew = newCubes.toMutableSet()
        val selected = mutableListOf<Candidate>()

        // Semantic equality has priority over source order and role. This is the second identity
        // layer after strict DNF equality.
        selectMaximumEquivalent(oldCubes, newCubes, candidates).forEach { candidate ->
            selected += candidate
            remainingOld -= candidate.old
            remainingNew -= candidate.new
        }

        // Pair the remaining cubes as edits only when their roles agree. Cross-role exact or
        // equivalent moves were already captured; arbitrary cross-role edits are clearer as
        // remove/add operations.
        candidates.asSequence()
            .filter { it.old.declarationKind == it.new.declarationKind }
            .filter { it.comparison is TaintAutomataComparison.Different }
            .sortedWith(candidateComparator)
            .forEach { candidate ->
                if (candidate.old in remainingOld && candidate.new in remainingNew) {
                    selected += candidate
                    remainingOld -= candidate.old
                    remainingNew -= candidate.new
                }
            }

        candidates.asSequence()
            .filter { it.comparison is TaintAutomataComparison.Inconclusive }
            .sortedWith(candidateComparator)
            .forEach { candidate ->
                if (candidate.old !in remainingOld || candidate.new !in remainingNew) return@forEach
                val value = candidate.comparison as TaintAutomataComparison.Inconclusive
                inconclusive += InconclusiveCubeComparison(
                    CubeReference.from(candidate.old),
                    CubeReference.from(candidate.new),
                    listOfNotNull(value.reason.name, value.detail).joinToString(": "),
                )
                remainingOld -= candidate.old
                remainingNew -= candidate.new
            }

        val matches = selected.map { candidate ->
            CubeMatch(
                candidate.old,
                candidate.new,
                if (candidate.comparison == TaintAutomataComparison.Equivalent) {
                    CubeMatch.Kind.AUTOMATA_EQUIVALENT
                } else {
                    CubeMatch.Kind.AUTOMATA_DIFFERENT
                },
            )
        }
        val reports = selected.map { candidate ->
            val witnesses = (candidate.comparison as? TaintAutomataComparison.Different)
                ?.witnesses.orEmpty()
            AutomataCubeMatch(
                CubeReference.from(candidate.old),
                CubeReference.from(candidate.new),
                candidate.comparison == TaintAutomataComparison.Equivalent,
                witnesses,
            )
        }
        return UnmatchedPairing(
            matches,
            reports,
            remainingNew.sortedWith(cubeComparator),
            remainingOld.sortedWith(cubeComparator),
            inconclusive.distinct(),
        )
    }

    private fun selectMaximumEquivalent(
        oldCubes: List<ContextualCube>,
        newCubes: List<ContextualCube>,
        candidates: List<Candidate>,
    ): List<Candidate> {
        val oldIndex = oldCubes.withIndex().associate { it.value to it.index }
        val newIndex = newCubes.withIndex().associate { it.value to it.index }
        val byPair = candidates.associateBy { oldIndex.getValue(it.old) to newIndex.getValue(it.new) }
        val allowed = candidates.asSequence()
            .filter { it.comparison == TaintAutomataComparison.Equivalent }
            .groupBy { oldIndex.getValue(it.old) }
            .mapValues { (_, values) -> values.sortedWith(candidateComparator).map { newIndex.getValue(it.new) } }
        val matchedOldByNew = IntArray(newCubes.size) { -1 }
        fun augment(old: Int, seen: BooleanArray): Boolean {
            for (new in allowed[old].orEmpty()) {
                if (seen[new]) continue
                seen[new] = true
                if (matchedOldByNew[new] == -1 || augment(matchedOldByNew[new], seen)) {
                    matchedOldByNew[new] = old
                    return true
                }
            }
            return false
        }
        oldCubes.indices.forEach { augment(it, BooleanArray(newCubes.size)) }
        return matchedOldByNew.withIndex().mapNotNull { (new, old) ->
            if (old < 0) null else byPair[old to new]
        }.sortedWith(candidateComparator)
    }

    private fun compareVariants(
        old: List<org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataEdges>,
        new: List<org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataEdges>,
    ): TaintAutomataComparison {
        if (old.size != new.size || old.isEmpty()) {
            return TaintAutomataComparison.Inconclusive(
                org.opentaint.semgrep.pattern.diff.automata.AutomataInconclusiveReason.VARIANT_COUNT_MISMATCH,
                "Compiled variant counts differ (old=${old.size}, new=${new.size})",
            )
        }
        val matrix = old.map { oldVariant ->
            new.map { newVariant -> comparator.compare(oldVariant, newVariant) }
        }
        if (hasPerfectVariantMatching(matrix) { it == TaintAutomataComparison.Equivalent }) {
            return TaintAutomataComparison.Equivalent
        }

        val couldStillMatch = hasPerfectVariantMatching(matrix) {
            it == TaintAutomataComparison.Equivalent || it is TaintAutomataComparison.Inconclusive
        }
        val firstInconclusive = matrix.flatten().filterIsInstance<TaintAutomataComparison.Inconclusive>()
            .firstOrNull()
        if (couldStillMatch && firstInconclusive != null) return firstInconclusive

        val witnesses = matrix.flatten().filterIsInstance<TaintAutomataComparison.Different>()
            .flatMap { it.witnesses }
            .distinct()
        return if (witnesses.isNotEmpty()) {
            TaintAutomataComparison.Different(witnesses)
        } else {
            firstInconclusive ?: TaintAutomataComparison.Inconclusive(
                org.opentaint.semgrep.pattern.diff.automata.AutomataInconclusiveReason.UNSUPPORTED_NONDETERMINISTIC_REGISTER_AUTOMATON,
            )
        }
    }

    private fun hasPerfectVariantMatching(
        matrix: List<List<TaintAutomataComparison>>,
        allowed: (TaintAutomataComparison) -> Boolean,
    ): Boolean {
        val matchedOldByNew = IntArray(matrix.size) { -1 }
        fun augment(oldIndex: Int, seen: BooleanArray): Boolean {
            for (newIndex in matrix.indices) {
                if (seen[newIndex] || !allowed(matrix[oldIndex][newIndex])) continue
                seen[newIndex] = true
                if (matchedOldByNew[newIndex] == -1 || augment(matchedOldByNew[newIndex], seen)) {
                    matchedOldByNew[newIndex] = oldIndex
                    return true
                }
            }
            return false
        }
        return matrix.indices.all { augment(it, BooleanArray(matrix.size)) }
    }

    private fun structuralChanges(
        old: ParsedNormalRuleSnapshot,
        new: ParsedNormalRuleSnapshot,
        matches: List<CubeMatch>,
        added: List<ContextualCube>,
        removed: List<ContextualCube>,
    ): List<StructureChange> {
        val changes = mutableListOf<StructureChange>()
        if (old.rule::class != new.rule::class) {
            changes += StructureChange(StructureChangeKind.RULE_MODE_CHANGED, "Rule mode changed")
        }
        if (old.primitiveTracking != new.primitiveTracking) {
            changes += StructureChange(
                StructureChangeKind.PRIMITIVE_TRACKING_CHANGED,
                "Primitive tracking changed from ${old.primitiveTracking} to ${new.primitiveTracking}",
            )
        }
        if (compareMetadata && (old.metadata.message != new.metadata.message ||
            old.metadata.severity != new.metadata.severity || old.metadata.metadata != new.metadata.metadata
        )) {
            changes += StructureChange(StructureChangeKind.RULE_METADATA_CHANGED, "Rule metadata changed")
        }

        for (kind in RulePartKind.entries) {
            val oldCount = declarationCount(old, kind)
            val newCount = declarationCount(new, kind)
            if (oldCount != newCount) {
                changes += StructureChange(
                    StructureChangeKind.PART_COUNT_CHANGED,
                    "$kind declaration count changed from $oldCount to $newCount",
                )
            }
        }

        for (match in matches) {
            val oldRef = CubeReference.from(match.old)
            val newRef = CubeReference.from(match.new)
            if (match.old.declarationKind != match.new.declarationKind) {
                changes += StructureChange(
                    StructureChangeKind.PART_ROLE_CHANGED,
                    "Cube moved from ${match.old.declarationKind} to ${match.new.declarationKind}",
                    oldRef,
                    newRef,
                )
            }
            if (modifierKey(match.old.context) != modifierKey(match.new.context)) {
                changes += StructureChange(
                    StructureChangeKind.PART_MODIFIERS_CHANGED,
                    "Part modifiers changed from ${modifierKey(match.old.context)} to ${modifierKey(match.new.context)}",
                    oldRef,
                    newRef,
                )
            }
            if (match.kind != CubeMatch.Kind.EXACT) {
                changes += StructureChange(
                    StructureChangeKind.CUBE_EXPRESSION_CHANGED,
                    "Cube expression changed (${match.kind})",
                    oldRef,
                    newRef,
                )
            }
        }
        // Added/removed cube lists carry the detailed identities; this keeps structural changes at
        // declaration level while still ensuring such changes affect aggregate status.
        if (added.isNotEmpty() || removed.isNotEmpty()) {
            changes += StructureChange(
                StructureChangeKind.CUBE_EXPRESSION_CHANGED,
                "${removed.size} cube(s) removed and ${added.size} cube(s) added",
            )
        }
        return changes.distinct().sortedWith(compareBy({ it.kind.ordinal }, { it.detail }))
    }

    private fun declarationCount(snapshot: ParsedNormalRuleSnapshot, kind: RulePartKind): Int =
        when (val rule = snapshot.rule) {
            is SemgrepMatchingRule -> if (kind == RulePartKind.MATCHING) rule.rules.size else 0
            is SemgrepTaintRule -> when (kind) {
                RulePartKind.MATCHING -> 0
                RulePartKind.SOURCE -> rule.sources.size
                RulePartKind.SINK -> rule.sinks.size
                RulePartKind.PROPAGATOR -> rule.propagators.size
                RulePartKind.SANITIZER -> rule.sanitizers.size
            }
        }

    private fun modifierKey(context: CubeContext): String = when (context) {
        CubeContext.Matching -> "matching"
        is CubeContext.Source -> context.declaration.let {
            "source(exact=${it.exact},control=${it.control},bySideEffect=${it.bySideEffect},label=${it.label},requires=${it.requires})"
        }
        is CubeContext.Sink -> "sink(requires=${context.declaration.requires})"
        is CubeContext.Propagator -> context.declaration.let {
            "propagator(from=${it.from},to=${it.to},bySideEffect=${it.bySideEffect})"
        }
        is CubeContext.Sanitizer -> context.declaration.let {
            "sanitizer(exact=${it.exact},bySideEffect=${it.bySideEffect})"
        }
        is CubeContext.JoinOperand ->
            "join(${context.side},${context.joinMetaVar},${modifierKey(context.underlying)})"
    }

    private fun compileTrace(rule: ParsedNormalRuleSnapshot) = SemgrepRuleLoadTrace(
        rule.descriptor.qualifiedRuleId,
        rule.descriptor.shortRuleId,
    )

    private fun compileCube(
        cube: ContextualCube,
        rule: ParsedNormalRuleSnapshot,
    ): Result<CompiledCube> = compilationCache.getOrPut(cube) {
        runCatching { RuleCubeCompiler(strategy).compile(cube, rule, compileTrace(rule)) }
    }

    companion object {
        private val cubeComparator = compareBy<ContextualCube>(
            { it.declarationKind.ordinal }, { it.declarationOrdinal }, { it.cube.ordinal }, { it.cube.key.toString() }
        )
        private val candidateComparator = compareBy<Candidate>(
            { it.old.declarationKind != it.new.declarationKind },
            { it.old.declarationOrdinal != it.new.declarationOrdinal },
            { it.old.declarationKind.ordinal },
            { it.old.declarationOrdinal },
            { it.new.declarationOrdinal },
            { it.old.cube.ordinal },
            { it.new.cube.ordinal },
        )
    }
}
