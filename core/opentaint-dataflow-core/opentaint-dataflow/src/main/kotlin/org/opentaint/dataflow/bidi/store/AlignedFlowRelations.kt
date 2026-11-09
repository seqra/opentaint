package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*

/** A private correlated view, never published as a new relation. The caller owns
 * the complete interface and has already selected an admitted prefix provider. */
internal fun specializeNormalFlow(m: ApManager, source: InitialAp, flow: FlowTree,
                                  target: InitialAp): FlowTree? {
    if (!source.isFlow || source.tail != Tail.STAR || target.tail != Tail.STAR ||
        source.base != target.base || flow.layer != Layer.NORMAL || flow.tail != Tail.STAR ||
        !target.pathArray.startsWith(source.pathArray)) return null
    val shift = target.pathArray.drop(source.pathArray.size)
    val exclusion = source.exclusion.union(flow.exclusion)
    if (shift.isNotEmpty() && !exclusion.admits(shift[0])) return null
    val root = if (shift.isEmpty()) flow.root else {
        val suffix = FlowAlgebra.prepend(m, m.path(shift), FlowAlgebra.LEAF_NODE)
        FlowAlgebra.graft(flow.root, { !it.isEmpty }, suffix, m.cancellation) ?: return null
    }
    return m.flowTree(flow.base, Layer.NORMAL,
        if (shift.isEmpty()) exclusion else ExclusionSet.Empty,
        flow.markExclusion, root, Tail.STAR)
}

/** Remove only aligned NORMAL STAR/FLOW outputs. One input shift applies to
 * every selected output; no input/output Cartesian relation is constructed. */
internal fun removeAlignedFlowCovered(m: ApManager, initial: InitialAp, value: FlowTree,
                                     providers: Sequence<Pair<InitialAp, FlowTree>>): FlowTree? {
    if (!initial.isFlow || initial.tail != Tail.STAR || value.layer != Layer.NORMAL || value.tail != Tail.STAR)
        return value
    var root = value.root
    for ((input, flow) in providers) {
        m.cancellation.checkpoint()
        if (flow.base != value.base || !flow.markExclusion.isSubsetOf(value.markExclusion)) continue
        val view = specializeNormalFlow(m, input, flow, initial) ?: continue
        if (!view.exclusion.isSubsetOf(initial.exclusion.union(value.exclusion))) continue
        root = FlowAlgebra.minusNode(root, view.root, m.cancellation) ?: return null
    }
    return if (root === value.root) value else value.withRoot(root)
}

/** Exact-coordinate intersection; the authority already performed spatial coverage. */
internal fun finalMembershipPart(m: ApManager, offered: Facts, retained: Sequence<Facts>): Facts? {
    var result: Facts? = null
    for (row in retained) {
        if (offered.groupKey != row.groupKey) continue
        val part = when {
            offered is Reach && row is Reach -> offered
            offered is FlowTree && row is FlowTree -> {
                val removed = FlowAlgebra.minusNode(offered.root,row.root,m.cancellation)
                val root = if (removed == null) offered.root else
                    FlowAlgebra.minusNode(offered.root,removed,m.cancellation)
                root?.let { offered.withRoot(it) }
            }
            offered is TaintTree && row is TaintTree ->
                intersectTaintMask(offered.root,row.root,m.cancellation)?.let { offered.withRoot(it) }
            else -> null
        } ?: continue
        result = if (result == null) part else m.mergeAddDelta(checkNotNull(result),part).first
    }
    return result
}
