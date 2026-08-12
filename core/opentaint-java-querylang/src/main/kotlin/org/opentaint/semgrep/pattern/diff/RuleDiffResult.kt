package org.opentaint.semgrep.pattern.diff

import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.diff.automata.AutomataTraceWitness
import org.opentaint.semgrep.pattern.diff.load.ParsedRuleDescriptor

enum class RuleDiffStatus {
    EQUIVALENT,
    CHANGED,
    INCONCLUSIVE,
    LOAD_FAILED,
}

enum class StructureChangeKind {
    RULE_MODE_CHANGED,
    RULE_METADATA_CHANGED,
    PRIMITIVE_TRACKING_CHANGED,
    PART_COUNT_CHANGED,
    PART_ROLE_CHANGED,
    PART_MODIFIERS_CHANGED,
    CUBE_EXPRESSION_CHANGED,
    JOIN_REF_ADDED,
    JOIN_REF_REMOVED,
    JOIN_OPERATION_ADDED,
    JOIN_OPERATION_REMOVED,
    JOIN_RESOLUTION_CHANGED,
}

data class StructureChange(
    val kind: StructureChangeKind,
    val detail: String,
    val oldCube: CubeReference? = null,
    val newCube: CubeReference? = null,
)

data class CubeReference(
    val ownerRuleId: String,
    val partKind: RulePartKind,
    val declarationOrdinal: Int,
    val cubeOrdinal: Int,
    val patterns: List<String>,
) {
    companion object {
        fun from(cube: ContextualCube) = CubeReference(
            ownerRuleId = cube.ownerRuleId,
            partKind = cube.declarationKind,
            declarationOrdinal = cube.declarationOrdinal,
            cubeOrdinal = cube.cube.ordinal,
            patterns = cube.cube.key.patterns,
        )
    }
}

data class AutomataCubeMatch(
    val oldCube: CubeReference,
    val newCube: CubeReference,
    val equivalent: Boolean,
    val witnesses: List<AutomataTraceWitness> = emptyList(),
)

data class InconclusiveCubeComparison(
    val oldCube: CubeReference?,
    val newCube: CubeReference?,
    val reason: String,
)

data class RuleDiffResult(
    val schemaVersion: Int = 1,
    val status: RuleDiffStatus,
    val comparisonComplete: Boolean,
    val hasProvenChanges: Boolean,
    val oldRule: ParsedRuleDescriptor?,
    val newRule: ParsedRuleDescriptor?,
    val oldLoadTrace: SemgrepLoadTrace,
    val newLoadTrace: SemgrepLoadTrace,
    val structureChanges: List<StructureChange> = emptyList(),
    val exactCubeMatches: List<Pair<CubeReference, CubeReference>> = emptyList(),
    val automataCubeMatches: List<AutomataCubeMatch> = emptyList(),
    val addedCubes: List<CubeReference> = emptyList(),
    val removedCubes: List<CubeReference> = emptyList(),
    val traceSamples: List<AutomataTraceWitness> = emptyList(),
    val inconclusiveComparisons: List<InconclusiveCubeComparison> = emptyList(),
    val loadFailure: String? = null,
)
