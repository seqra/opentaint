package org.opentaint.dataflow.bidi.ap

internal const val NOT_IDENTITY = -1
internal const val PLAIN_IDENTITY = 0
internal const val PROTECTED_IDENTITY = 1

/** Recognize the whole canonical image, including typed headers and protection.
 * This is literal equality at one coordinate, not semantic prefix coverage. */
internal fun ApManager.identityKind(initial: InitialAp, f: Facts): Int {
    cancellation.checkpoint()
    if (initial.isZero || f.base != initial.base || !sameCanonicalInitialImage(initial, f)) return NOT_IDENTITY
    if (f !is TaintTree || f.nonSubsumable == null) return PLAIN_IDENTITY
    return if (sameSingleCoordinate(initial, f.nonSubsumable)) PROTECTED_IDENTITY else NOT_IDENTITY
}

/** Do not allocate path snapshots, patterns or leaf lists on admission. */
private fun <P : TrieLeaf> ApManager.singleLeafAt(root: TrieNode<P>, path: IntArray): P? {
    var node = root
    for (accessor in path) {
        cancellation.checkpoint()
        if (!node.leaf.isEmpty) return null
        val edges = node.accessorData ?: return null
        if (edges.size != 1 || edges[0] != accessor) return null
        node = node.childData!![0]
    }
    if (node.accessorData != null || node.leaf.isEmpty) return null
    return node.leaf
}

private fun ApManager.sameSingleCoordinate(i: InitialAp, root: TaintNode): Boolean {
    val mark = (i.mark as? MarkSlot.Concrete)?.mark ?: return false
    val leaf = singleLeafAt(root, i.pathData) ?: return false
    return if (i.tail == Tail.EXACT)
        leaf.any.isEmpty && leaf.exact.size == 1 && mark in leaf.exact
    else leaf.exact.isEmpty && leaf.any.size == 1 && mark in leaf.any
}

private fun sameCanonicalHeader(i: InitialAp, f: Facts): Boolean = when (i.mark) {
    is MarkSlot.Star -> f is FlowTree && f.tail == i.tail && f.exclusion == i.exclusion && f.markExclusion.isEmpty
    is MarkSlot.Concrete -> f is TaintTree &&
        f.anyTail == (if (i.tail == Tail.EXACT) Tail.ANY_TAINT else i.tail) &&
        f.exclusion == (if (i.tail == Tail.EXACT || i.tail == Tail.ANY) ExclusionSet.Empty else i.exclusion)
}

private fun ApManager.sameCanonicalInitialImage(i: InitialAp, f: Facts): Boolean {
    if (!sameCanonicalHeader(i, f)) return false
    return when (f) {
        is FlowTree -> singleLeafAt(f.root, i.pathData) == FlowLeaf.LEAF
        is TaintTree -> sameSingleCoordinate(i, f.root)
        is Reach -> false
    }
}

/** Diagnostic classification is called only for an enabled first full admission. */
internal fun literalImageFallbackReason(initial: InitialAp?, f: Facts): String = when {
    initial == null -> "unsupported-premise"
    f.base != initial.base -> "different-base"
    !sameCanonicalHeader(initial, f) -> "different-typed-header"
    else -> "nonliteral-tree-or-mask"
}

/** Restore a stored image without applying normalization or a new abstraction. */
internal fun initialImage(m: ApManager, i: InitialAp, layer: Layer, isProtected: Boolean): Facts {
    m.cancellation.checkpoint()
    check(!i.isZero)
    return when (val slot = i.mark) {
        is MarkSlot.Star -> {
            check(!isProtected)
            val root = FlowAlgebra.prepend(m, i.path, FlowAlgebra.LEAF_NODE)
            m.flowTree(i.base, layer, i.exclusion, MarkExclusions.EMPTY, root, i.tail)
        }
        is MarkSlot.Concrete -> {
            val marks = m.markSetOf(slot.mark)
            val leaf = if (i.tail == Tail.EXACT) m.taintLeaves(marks, MarkSet.EMPTY)
                else m.taintLeaves(MarkSet.EMPTY, marks)
            val root = m.taintAlg.prepend(m, i.path, m.taintAlg.leafNode(leaf))
            m.taintTree(i.base, layer, root, i.exclusion,
                if (i.tail == Tail.EXACT) Tail.ANY_TAINT else i.tail,
                nonSubsumable = if (isProtected) root else null)
        }
    }
}
