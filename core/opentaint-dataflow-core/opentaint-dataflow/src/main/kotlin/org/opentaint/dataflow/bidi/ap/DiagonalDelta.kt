package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase

/** An exact diagonal packet with a typed STAR or ANY conclusion.
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
    val tail: Tail = Tail.ANY,
    val exclusion: ExclusionSet = ExclusionSet.Empty,
) {
    init {
        require(initialShape.isFlow && (initialShape.tail == Tail.STAR || initialShape.tail == Tail.ANY)) { "A diagonal packet needs an admitted FLOW initial shape" }
        require(base != AccessPathBase.Zero && base !is AccessPathBase.CleanerTemporary) {
            "A diagonal packet has an ordinary nonzero conclusion base"
        }
        require(!geometry.isEmpty && !marks.isEmpty) { "A diagonal packet needs geometry and mark memberships" }
        require((tail == Tail.STAR || tail == Tail.ANY) && (tail == Tail.STAR || exclusion == ExclusionSet.Empty))
        marks.forEach { mark ->
            initialShape.manager.cancellation.checkpoint()
            require(mark != TaintMark.ZERO) {
                "A diagonal packet contains nonzero runtime atoms"
            }
        }
    }
}
