package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase

/** An exact FULL diagonal output packet. Its conclusion is ANY with Empty E.
 * Marks stay correlated with their own concrete initial; this is not a FLOW
 * premise with a TaintTree. One immutable geometry serves the exact mark mask.
 * Protection applies uniformly to this packet; partial flags use separate
 * packets or the existing scalar fallback. */
data class DiagonalDelta(
    val initialShape: InitialAp,
    val base: AccessPathBase,
    val layer: Layer,
    val geometry: FlowNode,
    val marks: MarkSet,
    val protected: Boolean,
) {
    init {
        require(initialShape.isFlow && initialShape.tail == Tail.STAR &&
            initialShape.exclusion == ExclusionSet.Empty) { "A diagonal packet needs a canonical FLOW initial shape" }
        require(base != AccessPathBase.Zero && base !is AccessPathBase.CleanerTemporary) {
            "A diagonal packet has an ordinary nonzero conclusion base"
        }
        require(!geometry.isEmpty && !marks.isEmpty) { "A diagonal packet needs geometry and mark memberships" }
        marks.forEach { mark ->
            initialShape.manager.cancellation.checkpoint()
            require(mark != TaintMark.ZERO && !initialShape.manager.marks.isGroup(mark)) {
                "A diagonal packet contains FULL marks only"
            }
        }
    }
}
