package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.graph.PortId

/** Private capability; unknown views and unsupported cells use native C5. */
internal interface PreparedScopeDemandView : ScopeDemandView {
    fun prepareDataPlan(exit: PortId, templates: List<Pattern>, policy: RestrictedInitialPolicy,
                        onEntryCheck: () -> Unit = {}): PreparedLocalDataPlan?
}

internal interface PreparedLocalDataPlan {
    val rowChecks: Int
    /** Immutable executable program count; rejected rows are not programs. */
    val outputProgramCount: Int
    fun intersect(original: PremiseKey, raw: Facts): List<Facts>?
    fun emptyForBase(base: AccessPathBase): Boolean
}

/** Match the exact native summary normalization without interning an initial. */
internal fun normalizedOriginalTemplates(original: PremiseKey, flow: Boolean): List<Pattern> =
    original.members.map { member ->
        val pattern = member.toPattern()
        if (flow && member.isFlow && pattern.fact.tail == Tail.EXACT)
            pattern.copy(fact = pattern.fact.copy(tail = Tail.STAR)) else pattern
    }
