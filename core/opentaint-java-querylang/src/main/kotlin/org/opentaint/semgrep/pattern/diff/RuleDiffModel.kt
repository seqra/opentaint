package org.opentaint.semgrep.pattern.diff

import org.opentaint.semgrep.pattern.Formula
import org.opentaint.semgrep.pattern.SemgrepTaintPropagator
import org.opentaint.semgrep.pattern.SemgrepTaintSanitizer
import org.opentaint.semgrep.pattern.SemgrepTaintSink
import org.opentaint.semgrep.pattern.SemgrepTaintSource
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.diff.structure.FormulaDnfCube

enum class RulePartKind {
    MATCHING,
    SOURCE,
    SINK,
    PROPAGATOR,
    SANITIZER,
}

enum class JoinSide {
    LEFT,
    RIGHT,
}

sealed interface CubeContext {
    data object Matching : CubeContext
    data class Source(val declaration: SemgrepTaintSource<Formula>) : CubeContext
    data class Sink(val declaration: SemgrepTaintSink<Formula>) : CubeContext
    data class Propagator(val declaration: SemgrepTaintPropagator<Formula>) : CubeContext
    data class Sanitizer(val declaration: SemgrepTaintSanitizer<Formula>) : CubeContext
    data class JoinOperand(
        val side: JoinSide,
        val joinMetaVar: MetavarAtom,
        val underlying: CubeContext,
    ) : CubeContext
}

data class ContextualCube(
    val ownerRuleId: String,
    val declarationKind: RulePartKind,
    val declarationOrdinal: Int,
    val cube: FormulaDnfCube,
    val context: CubeContext,
)

data class CubeMatch(
    val old: ContextualCube,
    val new: ContextualCube,
    val kind: Kind,
) {
    enum class Kind {
        EXACT,
        AUTOMATA_EQUIVALENT,
        AUTOMATA_DIFFERENT,
    }
}

data class CubeDiffPlan(
    val exactMatches: List<CubeMatch>,
    val unmatchedOld: List<ContextualCube>,
    val unmatchedNew: List<ContextualCube>,
)
