package org.opentaint.dataflow.bidi.ap

import java.util.ArrayDeque
import org.opentaint.dataflow.util.Cancellation

/** Exact output coordinates. An annotation is never part of ordinary Facts identity. */
fun TaintTree.withProtection(mask: TaintNode?, cancellation: Cancellation? = null): TaintTree {
    val kept = mask?.let { intersectTaintMask(it, root, cancellation) }
    if (kept === nonSubsumable) return this
    return TaintTree(base, layer, root, exclusion, anyTail, kept)
}

fun TaintTree.withoutProtection(): TaintTree =
    if (nonSubsumable == null) this else TaintTree(base, layer, root, exclusion, anyTail)

/** A plain value lets a pure AP operation transport the annotation without new observations. */
fun TaintTree.protectedPart(): TaintTree? = nonSubsumable?.let {
    TaintTree(base, layer, it, if (it.hasAny) exclusion else ExclusionSet.Empty,
        if (it.hasAny) anyTail else Tail.ANY_TAINT)
}

fun Facts.withoutProtection(): Facts = if (this is TaintTree) withoutProtection() else this

private class MaskFrame(val pair: NodePair<TaintLeaves>, var expanded: Boolean = false)

/** Restrict metadata to the exact surviving positions and marks. This walk is stack safe. */
internal fun intersectTaintMask(mask: TaintNode, kept: TaintNode, cancellation: Cancellation? = null): TaintNode? {
    if (mask === kept) return mask
    val memo = HashMap<NodePair<TaintLeaves>, TaintNode?>()
    val initial = NodePair(mask, kept)
    val stack = ArrayDeque<MaskFrame>()
    stack.addLast(MaskFrame(initial))
    while (stack.isNotEmpty()) {
        cancellation?.checkpoint()
        val frame = stack.peekLast()
        val pair = frame.pair
        if (memo.containsKey(pair)) { stack.removeLast(); continue }
        if (pair.a === pair.b) { memo[pair] = pair.a; stack.removeLast(); continue }
        if (!frame.expanded) {
            frame.expanded = true
            pair.a.accessorData?.forEachIndexed { i, accessor ->
                cancellation?.checkpoint()
                pair.b.child(accessor)?.let { child ->
                    val key = NodePair(pair.a.childData!![i], child)
                    if (!memo.containsKey(key)) stack.addLast(MaskFrame(key))
                }
            }
            continue
        }
        val exact = pair.a.leaf.exact intersect pair.b.leaf.exact
        val any = pair.a.leaf.any intersect pair.b.leaf.any
        val leaf = if (exact.isEmpty && any.isEmpty) TaintLeaves.EMPTY else TaintLeaves(exact, any)
        val accessors = ArrayList<Int>()
        val children = ArrayList<TaintNode>()
        pair.a.accessorData?.forEachIndexed { i, accessor ->
            cancellation?.checkpoint()
            pair.b.child(accessor)?.let { child ->
                memo[NodePair(pair.a.childData!![i], child)]?.let {
                    accessors += accessor; children += it
                }
            }
        }
        memo[pair] = if (leaf.isEmpty && children.isEmpty()) null
            else if (leaf == pair.a.leaf && children.size == (pair.a.childData?.size ?: 0) &&
                children.indices.all { children[it] === pair.a.childData!![it] }) pair.a
            else TrieNode(leaf, accessors.toIntArray(), children.toTypedArray(), false)
        stack.removeLast()
    }
    return memo[initial]
}

/** Merge annotation outputs by the same complete typed header as ordinary results. */
internal class ProtectionOutputs(private val m: ApManager) : ApOut {
    // An exact-only projection has canonical Empty E/ANY_TAINT even when its
    // ordinary sibling has ANY leaves. Exact annotations are header independent.
    private val exact = HashMap<Pair<org.opentaint.dataflow.ap.ifds.AccessPathBase, Layer>, TaintNode>()
    private val any = HashMap<GroupKey, TaintNode>()
    override fun markRequest(mark: TaintMark) = Unit
    private fun <K> add(store: MutableMap<K, TaintNode>, key: K, root: TaintNode?) {
        if (root == null) return
        store[key] = store[key]?.let { m.taintAlg.mergeAdd(it, root, m.cancellation) } ?: root
    }
    override fun result(f: Facts) {
        if (f !is TaintTree) return
        val ex = if (!f.root.hasAny) f.root else m.taintAlg.mapLeaves(f.root, m.cancellation) {
            m.taintLeaves(it.exact, MarkSet.EMPTY)
        }
        add(exact, f.base to f.layer, ex)
        if (f.root.hasAny) add(any, f.groupKey, m.taintAlg.mapLeaves(f.root, m.cancellation) {
            m.taintLeaves(MarkSet.EMPTY, it.any)
        })
    }
    fun attach(f: Facts): Facts {
        if (f !is TaintTree) return f
        var root = f.nonSubsumable
        for (offered in listOfNotNull(exact[f.base to f.layer], any[f.groupKey])) {
            root = root?.let { m.taintAlg.mergeAdd(it, offered, m.cancellation) } ?: offered
        }
        return if (root == null) f else f.withProtection(root, m.cancellation)
    }
}

internal fun ApManager.transportProtection(c: Facts, out: ApOut, operation: (Facts, ApOut) -> Unit) {
    val protected = (c as? TaintTree)?.protectedPart()
    if (protected == null) { operation(c, out); return }
    val masks = ProtectionOutputs(this)
    operation(protected, masks)
    operation(c, object : ApOut {
        override fun result(f: Facts) = out.result(masks.attach(f))
        override fun markRequest(mark: TaintMark) = out.markRequest(mark)
    })
}

internal fun ApManager.selectedProtection(f: Facts, selected: MarkSet?): Facts {
    if (f !is TaintTree) return f
    val selectedRoot = if (selected == null) f.root else taintAlg.mapLeaves(f.root, cancellation) {
        taintLeaves(it.exact intersect selected, it.any intersect selected)
    } ?: return f
    val root = f.nonSubsumable?.let { taintAlg.mergeAdd(it, selectedRoot, cancellation) } ?: selectedRoot
    return f.withProtection(root, cancellation)
}

/** Selection/filter operations keep coordinates and only remove memberships. */
internal fun retainProtection(input: Facts, result: Facts, cancellation: Cancellation? = null): Facts =
    if (input !is TaintTree || result !is TaintTree || input.nonSubsumable == null) result
    else result.withProtection(input.nonSubsumable, cancellation)
