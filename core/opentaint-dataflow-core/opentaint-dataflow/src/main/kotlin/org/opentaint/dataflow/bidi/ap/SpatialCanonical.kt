package org.opentaint.dataflow.bidi.ap

import java.util.ArrayDeque

/** One immutable DAG node can occur below different admitted ancestors. */
private class SpatialKey<P : TrieLeaf>(val node: TrieNode<P>, val above: P) {
    private val hash = System.identityHashCode(node) * 31 + above.hashCode()
    override fun hashCode(): Int = hash
    override fun equals(other: Any?): Boolean = other is SpatialKey<*> && node === other.node && above == other.above
}
private class SpatialFrame<P : TrieLeaf>(val key: SpatialKey<P>, var expanded: Boolean = false)

/** Same-tail prefix normalization. E is read only on the first step below a
 * newly encountered span; prior inherited coverage persists across later E. */
private fun <P : TrieLeaf> LeafAlgebra<P>.canonicalSpans(
    root: TrieNode<P>, exclusion: ExclusionSet, m: ApManager,
    belowSpan: (P) -> P, samePoint: (P) -> P = { it },
): TrieNode<P> {
    val results = HashMap<SpatialKey<P>, TrieNode<P>?>()
    val start = SpatialKey(root, empty)
    val stack = ArrayDeque<SpatialFrame<P>>()
    stack.addLast(SpatialFrame(start))
    while (stack.isNotEmpty()) {
        m.cancellation.checkpoint()
        val frame = stack.peekLast()
        val key = frame.key
        if (results.containsKey(key)) { stack.removeLast(); continue }
        val next = union(key.above, belowSpan(key.node.leaf))
        if (!frame.expanded) {
            frame.expanded = true
            key.node.accessorData?.forEachIndexed { i, accessor ->
                val child = SpatialKey(key.node.childData!![i], if (exclusion.admits(accessor)) next else key.above)
                if (!results.containsKey(child)) stack.addLast(SpatialFrame(child))
            }
        } else {
            val leaf = samePoint(minus(key.node.leaf, key.above))
            results[key] = mapChildren(key.node, leaf, m.cancellation) { accessor, child ->
                results.getValue(SpatialKey(child, if (exclusion.admits(accessor)) next else key.above))
            }
            stack.removeLast()
        }
    }
    return checkNotNull(results.getValue(start)) { "A nonempty packet has a minimal retained position" }
}

/** Explicit MAY positions guide later refinement even when an ancestor covers
 * their denotation. This applies to real FLOW packets, not TAINT geometry. */
internal fun FlowTree.keepsDemandPositions(): Boolean = layer == Layer.DEMAND && tail == Tail.ANY

internal fun ApManager.canonicalFlowPacket(value: FlowTree): FlowTree =
    if (value.keepsDemandPositions()) value else canonicalFlowDataPacket(value)

/** DATA normalization is also used by packed TAINT's temporary FLOW geometry. */
internal fun ApManager.canonicalFlowDataPacket(value: FlowTree): FlowTree {
    if (value.tail != Tail.ANY && value.tail != Tail.ANY_TAINT) return value
    if (value.root.childData == null) return value
    val root = FlowAlgebra.canonicalSpans(value.root, value.exclusion, this, { it })
    return if (root === value.root) value else value.withRoot(root)
}

internal fun ApManager.canonicalTaintPacket(value: TaintTree): TaintTree {
    if (value.anyTail != Tail.ANY && value.anyTail != Tail.ANY_TAINT || !value.root.hasAny) return value
    if (value.root.childData == null && (value.anyTail != Tail.ANY || value.root.leaf.exact.isEmpty)) return value
    val may = value.anyTail == Tail.ANY
    fun below(leaf: TaintLeaves) = taintLeaves(if (may) leaf.any else MarkSet.EMPTY, leaf.any)
    fun at(leaf: TaintLeaves) = if (may) taintLeaves(leaf.exact - leaf.any, leaf.any) else leaf
    val ordinary = taintAlg.canonicalSpans(value.root, value.exclusion, this, ::below, ::at)
    val protection = value.nonSubsumable?.let {
        taintAlg.canonicalSpans(it, value.exclusion, this, ::below, ::at)
    }
    // Native masks require coordinate inclusion even when plain ancestor
    // support is spatially broader than the protected dependency.
    val root = if (protection == null) ordinary else taintAlg.mergeAdd(ordinary, protection, cancellation)
    return if (root === value.root && protection === value.nonSubsumable) value
        else taintTree(value.base, value.layer, root, value.exclusion, value.anyTail, protection)
}

/** Packet-local canonical C2 input. The list contract also supports callers
 * consuming the multi-header deltas returned by canonical group admission. */
fun ApManager.canonicalPackets(value: Facts): List<Facts> = listOf(when (value) {
    is Reach -> value
    is FlowTree -> canonicalFlowPacket(value)
    is TaintTree -> canonicalTaintPacket(value)
})

/** A cohort changes no semantic key: channel is mx for FLOW and Unit for a
 * concrete mark-mask stream. E remains a separate rooted-region payload. */
internal data class SpatialRegion<P : TrieLeaf, K>(
    val tail: Tail, val exclusion: ExclusionSet, val channel: K, val root: TrieNode<P>,
)
private data class SpatialHeader<K>(val tail: Tail, val exclusion: ExclusionSet, val channel: K)

private fun <P : TrieLeaf> LeafAlgebra<P>.intersectionAt(
    a: TrieNode<P>, b: TrieNode<P>, m: ApManager,
): TrieNode<P>? {
    if (a === b) return a
    val outside = minusNode(a, b, m.cancellation) ?: return a
    return minusNode(a, outside, m.cancellation)
}

private class FillKey<P : TrieLeaf>(val parent: TrieNode<P>, val child: TrieNode<P>?) {
    private val hash = System.identityHashCode(parent) * 31 + System.identityHashCode(child)
    override fun hashCode(): Int = hash
    override fun equals(other: Any?): Boolean = other is FillKey<*> && parent === other.parent && child === other.child
}
private class FillFrame<P : TrieLeaf>(val key: FillKey<P>, var expanded: Boolean = false)

/** Partition only the leaf masks whose complete immediate child fills E.
 * The pair DAG memo avoids path enumeration, including shared subtrees. */
private fun <P : TrieLeaf> LeafAlgebra<P>.fillImmediate(
    parent: TrieNode<P>, completeChildren: TrieNode<P>, exclusion: ExclusionSet.Concrete, m: ApManager,
): Map<ExclusionSet, TrieNode<P>> {
    val results = HashMap<FillKey<P>, Map<ExclusionSet, TrieNode<P>>>()
    val start = FillKey(parent, completeChildren)
    val stack = ArrayDeque<FillFrame<P>>()
    stack.addLast(FillFrame(start))
    while (stack.isNotEmpty()) {
        m.cancellation.checkpoint()
        val frame = stack.peekLast()
        val key = frame.key
        if (results.containsKey(key)) { stack.removeLast(); continue }
        if (key.child == null) {
            results[key] = mapOf(exclusion to key.parent)
            stack.removeLast()
            continue
        }
        if (!frame.expanded) {
            frame.expanded = true
            key.parent.accessorData?.forEachIndexed { i, field ->
                val childKey = FillKey(key.parent.childData!![i], key.child.child(field))
                if (!results.containsKey(childKey)) stack.addLast(FillFrame(childKey))
            }
        } else {
            var leaves = linkedMapOf<ExclusionSet, P>()
            if (!key.parent.leaf.isEmpty) leaves[exclusion] = key.parent.leaf
            for (field in exclusion.data) {
                m.cancellation.checkpoint()
                val support = key.child.child(field)?.leaf ?: continue
                if (support.isEmpty) continue
                val split = LinkedHashMap<ExclusionSet, P>()
                for ((e, leaf) in leaves) {
                    val yes = minus(leaf, minus(leaf, support))
                    val no = minus(leaf, support)
                    if (!no.isEmpty) split[e] = split[e]?.let { union(it, no) } ?: no
                    if (!yes.isEmpty) {
                        val next = m.intern(ExclusionSet.of((e as? ExclusionSet.Concrete)?.data
                            ?.filter { it != field }?.toIntArray() ?: EMPTY_PATH))
                        split[next] = split[next]?.let { union(it, yes) } ?: yes
                    }
                }
                leaves = split
            }
            val headers = LinkedHashSet<ExclusionSet>()
            headers.addAll(leaves.keys)
            key.parent.accessorData?.forEachIndexed { i, field ->
                headers.addAll(results.getValue(FillKey(key.parent.childData!![i], key.child.child(field))).keys)
            }
            val out = LinkedHashMap<ExclusionSet, TrieNode<P>>()
            for (e in headers) {
                val fields = ArrayList<Int>()
                val children = ArrayList<TrieNode<P>>()
                var unchanged = e == exclusion
                key.parent.accessorData?.forEachIndexed { i, field ->
                    val old = key.parent.childData!![i]
                    val child = results.getValue(FillKey(old, key.child.child(field)))[e]
                    unchanged = unchanged && child === old
                    if (child != null) { fields += field; children += child }
                }
                val leaf = leaves[e] ?: empty
                val result = if (unchanged && leaf == key.parent.leaf) key.parent
                    else node(leaf, fields.toIntArray(), children.toTypedArray())
                if (!result.isEmpty) out[e] = result
            }
            results[key] = out
            stack.removeLast()
        }
    }
    return results.getValue(start)
}

private fun <P : TrieLeaf, K> LeafAlgebra<P>.coalesceRegions(
    values: List<SpatialRegion<P, K>>, m: ApManager,
): List<SpatialRegion<P, K>> {
    val roots = LinkedHashMap<SpatialHeader<K>, TrieNode<P>>()
    for (v in values) {
        m.cancellation.checkpoint()
        if (v.root.isEmpty) continue
        val key = SpatialHeader(v.tail, v.exclusion, v.channel)
        roots[key] = roots[key]?.let { mergeAdd(it, v.root, m.cancellation) } ?: v.root
    }
    return roots.map { (h, root) -> SpatialRegion(h.tail, h.exclusion, h.channel, root) }
}

/** Constructive region rules from Canonical.lean, executed over packed DAGs.
 * FLOW channels never split into positive mark sets: caller-supplied full
 * channel support is required for a cover or a complete-child fill. */
internal fun <P : TrieLeaf, K> LeafAlgebra<P>.canonicalRegions(
    input: List<SpatialRegion<P, K>>, m: ApManager,
    equalEJoin: ((K,K) -> K)? = null,
    preserveAnyHeads: Boolean = false,
    channelCovers: (K, K) -> Boolean,
): List<SpatialRegion<P, K>> {
    var current = coalesceRegions(input, m)
    while (true) {
        m.cancellation.checkpoint()
        // Equal E makes the cofinite payload union exactly representable.
        // Join only shared coordinates; unrelated geometry keeps its old mx.
        var channelJoined = false
        if (equalEJoin != null) channelJoin@ for (i in current.indices) {
            val a = current[i]
            if (a.tail != Tail.ANY && a.tail != Tail.ANY_TAINT) continue
            for (j in i + 1 until current.size) {
                val b = current[j]
                if (b.tail != a.tail || b.exclusion != a.exclusion || b.channel == a.channel) continue
                val common = intersectionAt(a.root,b.root,m) ?: continue
                val next = ArrayList<SpatialRegion<P,K>>(current.size + 1)
                for (k in current.indices) if (k != i && k != j) next += current[k]
                minusNode(a.root,common,m.cancellation)?.let { next += a.copy(root = it) }
                minusNode(b.root,common,m.cancellation)?.let { next += b.copy(root = it) }
                next += a.copy(channel = equalEJoin(a.channel,b.channel),root = common)
                current = coalesceRegions(next,m)
                channelJoined = true
                break@channelJoin
            }
        }
        if (channelJoined) continue
        // Join shared coordinates of same-channel MUST cohorts by E intersection.
        var joined = false
        join@ for (i in current.indices) {
            val a = current[i]
            if (a.tail != Tail.ANY_TAINT) continue
            for (j in i + 1 until current.size) {
                val b = current[j]
                if (b.tail != a.tail || b.channel != a.channel || b.exclusion == a.exclusion) continue
                val common = intersectionAt(a.root, b.root, m) ?: continue
                val next = ArrayList<SpatialRegion<P, K>>(current.size + 1)
                for (k in current.indices) if (k != i && k != j) next += current[k]
                minusNode(a.root, common, m.cancellation)?.let { next += a.copy(root = it) }
                minusNode(b.root, common, m.cancellation)?.let { next += b.copy(root = it) }
                next += a.copy(exclusion = m.intern(a.exclusion.intersect(b.exclusion)), root = common)
                current = coalesceRegions(next, m)
                joined = true
                break@join
            }
        }
        if (joined) continue
        // A child channel must supply ALL parent marks. Narrower FLOW children
        // remain separate; concrete masks split only their already finite bits.
        var filled = false
        fill@ for (i in current.indices) {
            val parent = current[i]
            val e = parent.exclusion as? ExclusionSet.Concrete ?: continue
            if (parent.tail != Tail.ANY_TAINT) continue
            for (j in current.indices) {
                val child = current[j]
                if (child.tail != Tail.ANY_TAINT || child.exclusion != ExclusionSet.Empty ||
                    !channelCovers(child.channel, parent.channel)) continue
                val split = fillImmediate(parent.root, child.root, e, m)
                if (split.size == 1 && split[e] === parent.root) continue
                val next = ArrayList<SpatialRegion<P, K>>(current.size + split.size)
                for (k in current.indices) if (k != i) next += current[k]
                for ((nextE, root) in split) next += parent.copy(exclusion = nextE, root = root)
                current = coalesceRegions(next, m)
                filled = true
                break@fill
            }
        }
        if (filled) continue
        // New prefix coverage applies to compatible equal tail kinds. The
        // original admission path still owns its pre-existing cross-tail law.
        val next = ArrayList<SpatialRegion<P, K>>(current.size)
        var changed = false
        for (i in current.indices) {
            val value = current[i]
            val keepHeads = preserveAnyHeads && value.tail == Tail.ANY
            var root: TrieNode<P>? = if (!keepHeads && (value.tail == Tail.ANY || value.tail == Tail.ANY_TAINT))
                canonicalSpans(value.root, value.exclusion, m, { it }) else value.root
            for (j in current.indices) {
                if (i == j || root == null) continue
                val stored = current[j]
                if (stored.tail != value.tail || !channelCovers(stored.channel, value.channel)) continue
                val sameAt = stored.tail == Tail.ANY || stored.exclusion.isSubsetOf(value.exclusion)
                val equivalent = sameAt && (stored.tail == Tail.ANY || value.exclusion.isSubsetOf(stored.exclusion)) &&
                    channelCovers(value.channel, stored.channel)
                // Equivalent cohort headers can overlap at coordinates. Keep
                // their first witness, never subtract the same point twice.
                val atAllowed = sameAt && (!equivalent || j < i)
                val belowAllowed = !keepHeads && (stored.tail == Tail.ANY || stored.tail == Tail.ANY_TAINT)
                root = subtract(root, stored.root, empty,
                    at = { if (atAllowed) it else empty },
                    below = { if (belowAllowed) it else empty },
                    admits = stored.exclusion::admits, cancellation = m.cancellation)
            }
            changed = changed || root !== value.root
            if (root != null) next += value.copy(root = root)
        }
        if (!changed) return current
        current = coalesceRegions(next, m)
    }
}

internal fun ApManager.canonicalFlowState(values: List<FlowTree>): List<FlowTree> {
    if (values.isEmpty()) return values
    val first = values[0]
    return FlowAlgebra.canonicalRegions(values.map {
        check(it.base == first.base && it.layer == first.layer)
        SpatialRegion(it.tail,it.exclusion,it.markExclusion,it.root)
    },this,equalEJoin = { a,b -> intern(a.intersect(b)) },preserveAnyHeads = first.layer == Layer.DEMAND,
        channelCovers = MarkExclusions::isSubsetOf).map { flowTree(first.base, first.layer, it.exclusion, it.channel, it.root, it.tail) }
}

private data class TaintSpatialHeader(val tail: Tail, val exclusion: ExclusionSet)
private class TaintSpatialRoots(var ordinary: TaintNode? = null, var protected: TaintNode? = null)

internal fun ApManager.canonicalTaintState(values: List<TaintTree>): List<TaintTree> {
    if (values.isEmpty()) return values
    val first = values[0]
    fun union(a: TaintNode?, b: TaintNode?): TaintNode? = when {
        a == null -> b
        b == null -> a
        else -> taintAlg.mergeAdd(a,b,cancellation)
    }
    fun extract(root: TaintNode, any: Boolean): TaintNode? = taintAlg.mapCanonicalLeaves(root,cancellation) {
        if (any) taintLeaves(MarkSet.EMPTY,it.any) else taintLeaves(it.exact,MarkSet.EMPTY)
    }
    val ordinary = ArrayList<SpatialRegion<TaintLeaves,Unit>>()
    val protected = ArrayList<SpatialRegion<TaintLeaves,Unit>>()
    val exactHeaders = LinkedHashMap<TaintSpatialHeader,TaintSpatialRoots>()
    // Only byte-equal whole ordinary content has the old T4 mixed-header join.
    val contentE = HashMap<Pair<Tail,TaintNode>,ExclusionSet>()
    for (value in values) {
        cancellation.checkpoint()
        check(value.base == first.base && value.layer == first.layer)
        val header = TaintSpatialHeader(value.anyTail,value.exclusion)
        val exact = exactHeaders.getOrPut(header,::TaintSpatialRoots)
        exact.ordinary = union(exact.ordinary,extract(value.root,false))
        extract(value.root,true)?.let { ordinary += SpatialRegion(value.anyTail,value.exclusion,Unit,it) }
        if (value.root.hasAny) {
            val key = value.anyTail to value.root
            contentE[key] = contentE[key]?.intersect(value.exclusion) ?: value.exclusion
        }
        value.nonSubsumable?.let { flags ->
            exact.protected = union(exact.protected,extract(flags,false))
            extract(flags,true)?.let { protected += SpatialRegion(value.anyTail,value.exclusion,Unit,it) }
        }
    }
    val ordinarySpans = taintAlg.canonicalRegions(ordinary,this) { _,_ -> true }
    val protectedSpans = taintAlg.canonicalRegions(protected,this) { _,_ -> true }
    fun pruneExact(root: TaintNode?, spans: List<SpatialRegion<TaintLeaves,Unit>>): TaintNode? {
        var current = root
        for (span in spans) if (span.tail == Tail.ANY && current != null) {
            current = taintAlg.subtract(current,span.root,TaintLeaves.EMPTY,
                at = { taintLeaves(it.any,MarkSet.EMPTY) }, below = { taintLeaves(it.any,MarkSet.EMPTY) },
                cancellation = cancellation)
        }
        return current
    }
    val grouped = LinkedHashMap<TaintSpatialHeader,TaintSpatialRoots>()
    for (span in ordinarySpans) {
        val roots = grouped.getOrPut(TaintSpatialHeader(span.tail,span.exclusion),::TaintSpatialRoots)
        roots.ordinary = union(roots.ordinary,span.root)
    }
    for (span in protectedSpans) {
        val roots = grouped.getOrPut(TaintSpatialHeader(span.tail,span.exclusion),::TaintSpatialRoots)
        roots.protected = union(roots.protected,span.root)
    }
    var seenExact: TaintNode? = null
    var seenProtectedExact: TaintNode? = null
    for ((oldHeader,exact) in exactHeaders) {
        var destination = oldHeader.takeIf { it in grouped }
        if (destination == null) {
            // Keep unchanged exact coordinates in their old mixed cohort where
            // possible. A real equal-content T4 join may move that cohort.
            for (value in values) if (value.anyTail == oldHeader.tail && value.exclusion == oldHeader.exclusion && value.root.hasAny) {
                val joined = TaintSpatialHeader(value.anyTail,contentE.getValue(value.anyTail to value.root))
                if (joined in grouped) { destination = joined; break }
            }
        }
        val header = destination ?: TaintSpatialHeader(Tail.ANY_TAINT,ExclusionSet.Empty)
        val ordinaryExact = pruneExact(exact.ordinary,ordinarySpans)?.let { root ->
            if (seenExact == null) root else taintAlg.minusNode(root,checkNotNull(seenExact),cancellation)
        }
        val protectedExact = pruneExact(exact.protected,protectedSpans)?.let { root ->
            if (seenProtectedExact == null) root else taintAlg.minusNode(root,checkNotNull(seenProtectedExact),cancellation)
        }
        if (ordinaryExact == null && protectedExact == null) continue
        val roots = grouped.getOrPut(header,::TaintSpatialRoots)
        roots.ordinary = union(roots.ordinary,ordinaryExact)
        roots.protected = union(roots.protected,protectedExact)
        seenExact = union(seenExact,ordinaryExact)
        seenProtectedExact = union(seenProtectedExact,protectedExact)
    }
    return grouped.mapNotNull { (header,roots) ->
        val root = union(roots.ordinary,roots.protected) ?: return@mapNotNull null
        taintTree(first.base,first.layer,root,header.exclusion,header.tail,roots.protected)
    }
}

/** Read current exact coordinates, not semantic ancestor coverage. A final
 * detached batch cannot retain a removed descendant through its old snapshot.
 * Exact TAINT slots ignore a wrapper's any-tail/E, as native scalar leaves do. */
fun retainCurrentFacts(m: ApManager, offered: Facts, current: Iterable<Facts>): List<Facts> {
    m.cancellation.checkpoint()
    return when (offered) {
        is Reach -> if (current.any { it is Reach && it.layer == offered.layer }) listOf(offered) else emptyList()
        is FlowTree -> {
            var root: FlowNode? = null
            for (value in current) {
                m.cancellation.checkpoint()
                if (value !is FlowTree || value.groupKey != offered.groupKey) continue
                val common = FlowAlgebra.intersectionAt(offered.root,value.root,m) ?: continue
                root = root?.let { FlowAlgebra.mergeAdd(it,common,m.cancellation) } ?: common
            }
            root?.let { listOf(offered.withRoot(it)) } ?: emptyList()
        }
        is TaintTree -> {
            var ordinary: TaintNode? = null
            var protected: TaintNode? = null
            fun selected(value: TaintTree, root: TaintNode): TaintNode? {
                val matching = value.anyTail == offered.anyTail && value.exclusion == offered.exclusion
                return if (matching) root else m.taintAlg.mapCanonicalLeaves(root,m.cancellation) {
                    m.taintLeaves(it.exact,MarkSet.EMPTY)
                }
            }
            for (value in current) {
                m.cancellation.checkpoint()
                if (value !is TaintTree || value.base != offered.base || value.layer != offered.layer) continue
                selected(value,value.root)?.let { mask ->
                    intersectTaintMask(offered.root,mask,m.cancellation)?.let { common ->
                        ordinary = ordinary?.let { m.taintAlg.mergeAdd(it,common,m.cancellation) } ?: common
                    }
                }
                if (offered.nonSubsumable != null && value.nonSubsumable != null) {
                    selected(value,value.nonSubsumable)?.let { mask ->
                        intersectTaintMask(offered.nonSubsumable,mask,m.cancellation)?.let { common ->
                            protected = protected?.let { m.taintAlg.mergeAdd(it,common,m.cancellation) } ?: common
                        }
                    }
                }
            }
            ordinary?.let { listOf(m.taintTree(offered.base,offered.layer,it,offered.exclusion,offered.anyTail,protected)) }
                ?: emptyList()
        }
    }
}
