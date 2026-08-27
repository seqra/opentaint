package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.createNodeFromAccessors
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.util.forEachEntry
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.dataflow.util.getOrCreateNullable
import org.opentaint.dataflow.util.int2ObjectMap
import java.util.IdentityHashMap

abstract class AccessBasedStorage<S : AccessBasedStorage<S>>(
    val manager: TreeApManager
) {
    private val children = int2ObjectMap<S?>()

    abstract fun createStorage(): S

    fun getOrCreateNode(access: AccessPath.AccessNode?): S {
        if (access == null) {
            @Suppress("UNCHECKED_CAST")
            return this as S
        }

        var storage = this
        access.toList().forEachInt { accessor ->
            storage = storage.getOrCreateChild(accessor)
        }

        @Suppress("UNCHECKED_CAST")
        return storage as S
    }

    fun find(access: AccessPath.AccessNode?): S? {
        if (access == null) {
            @Suppress("UNCHECKED_CAST")
            return this as S
        }

        var storage = this
        access.toList().forEachInt { accessor ->
            storage = storage.findChild(accessor) ?: return null
        }

        @Suppress("UNCHECKED_CAST")
        return storage as S
    }

    fun filterContains(pattern: AccessTree.AccessNode): Sequence<S> {
        val nodes = ContainsNodeCollector<S>()
        collectNodesContains(pattern, nodes)
        return nodes.asSequence()
    }

    /**
     * The premises a caller fact activates: every trie node whose key path is a prefix of the fact.
     * The current node is added at EVERY level, which is why a premise that is a proper prefix of
     * the fact fires alongside the most specific one.
     *
     * The `[any]` arm ([collectNodesContainsAnyAccessor]) is applied here rather than in one
     * storage's override, which is a behaviour change for `FactSideEffectSummariesTreeApStorage`
     * and `SideEffectRequirementTreeApStorage` (design 6.7). Those two had no `[any]` handling at
     * all, so an `[any]`-carrying caller fact activated only the trie root and no concrete
     * side-effect premise below it. That is a loss, not a deliberate narrowing: everything
     * downstream of the lookup -- `AccessTree.delta`, `hasEmptyDelta`, `filterStartsWith` -- reads
     * `[any]` correctly through `AccessTree.AccessNode.getChild`, so the filter was the only step
     * that treated `[any]` as an opaque literal. The only thing that recovered the missed premise
     * was the PUSH path (`MethodTreeAccessPathSubscription`, which uses `filterStartsWith`), and
     * that only fires when the callee's summary is recorded after the caller subscribed -- an
     * ordering accident, not a mechanism.
     */
    private fun collectNodesContains(pattern: AccessTree.AccessNode, nodes: ContainsNodeCollector<S>) {
        @Suppress("UNCHECKED_CAST")
        nodes.add(this as S)

        if (pattern.isFinal) {
            children.get(FINAL_ACCESSOR_IDX)?.let { nodes.add(it) }
        }

        pattern.forEachAccessor { accessor, accessorPattern ->
            collectNodesContainsAccessor(accessorPattern, accessor, nodes)
        }
    }

    private fun collectNodesContainsAccessor(
        pattern: AccessTree.AccessNode,
        accessor: AccessorIdx,
        nodes: ContainsNodeCollector<S>
    ) {
        if (accessor == ANY_ACCESSOR_IDX) {
            collectNodesContainsAnyAccessor(pattern, nodes)
            return
        }

        children.get(accessor)?.collectNodesContains(pattern, nodes)
    }

    /**
     * Premise lookup for a caller fact whose accessor at THIS storage node is `[any]`, with
     * [pattern] the fact's sub-tree below that `[any]`.
     *
     * This is the ONE `[any]` rule, shared by every trie built on this class -- the F2F summaries,
     * the fact side-effect summaries and the side-effect requirements. It used to be a per-storage
     * override (`MethodInitialToFinalApSummaries`, `nodes += allNodes()`), which is why the other
     * two storages had no expansion arm at all; see the note on [collectNodesContains] for why the
     * asymmetry was not defensible. Nothing here is exposed: the whole traversal is private.
     *
     * `[any]` denotes ZERO OR MORE steps of the kinds [TreeApManager.isCoveredByAny] accepts, so the
     * premises a fact `[any]` activates are the union of three families. The rule mirrors the
     * fact-side reader, `AccessTree.AccessNode.getChild`, which is what `AccessTree.delta`
     * -- the exact test that decides whether a premise really applies -- uses downstream:
     *
     *  - **zero steps**: the `[any]` absorbs nothing and [pattern] applies right here. This is
     *    `getChild(c)`'s `anyAccessorNode.getNodeByAccessor(c)` term.
     *  - **structural**: the trie's literal `[any]` child, descended with [pattern], pattern-directed.
     *    This is `getChild(ANY_ACCESSOR_IDX)`, which resolves to exactly the fact's sub-node below
     *    its own `[any]` -- note it does NOT re-prepend the `[any]`, so a premise `[any]` link
     *    consumes the fact's `[any]` outright and the two arms below do not apply under it.
     *  - **expansion**: the `[any]` absorbs one covered step and stays in force below it, so every
     *    trie child keyed by a covered accessor is re-entered with the SAME `[any]`-rooted pattern.
     *    This is `getChild(c)`'s `anyAccessorNoRepeats.addParentIfPossible(ANY_ACCESSOR_IDX)` term.
     *    **Under [TreeApManager.literalAnyMatch] this arm is gone**, exactly as the corresponding
     *    term is gone from `AccessTree.AccessNode.getChildMatching`. It is the one arm that returns
     *    a premise the fact does not hold literally, and it is the lookup half of the ratchet the
     *    literal rule removes -- keeping it here would hand `delta` premises it now refuses, which
     *    is pure work. The other two arms are what the fact really holds.
     *
     * A child keyed by an accessor [TreeApManager.isCoveredByAny] rejects -- a taint mark, a static,
     * a type-info accessor, `[value]`, `[final]` -- is NOT expanded into: the `[any]` provably
     * cannot reach it. It is still reachable through the zero-step arm if [pattern] names it
     * literally, which is the only way the fact can actually denote it.
     *
     * Terminates: the expansion arm recurses on strictly deeper trie children with an unchanged
     * pattern, and the trie is a finite tree, so that arm bottoms out at the trie's height, visiting
     * each descendant at most once. The other two arms hand off to [collectNodesContains], which
     * consumes one pattern level per trie level; it can re-enter here only through a nested `[any]`
     * in the pattern, and then with a strictly smaller pattern. So (trie depth remaining, pattern
     * depth remaining) decreases lexicographically on every recursive step.
     */
    private fun collectNodesContainsAnyAccessor(
        pattern: AccessTree.AccessNode,
        nodes: ContainsNodeCollector<S>
    ) {
        collectNodesContains(pattern, nodes)

        children.get(ANY_ACCESSOR_IDX)?.collectNodesContains(pattern, nodes)

        if (manager.literalAnyLookup) return

        children.forEachEntry { accessor, child ->
            if (child == null) return@forEachEntry

            // `isCoveredByAny(ANY_ACCESSOR_IDX)` is false by design (AccessTree.kt) and asking the
            // injected strategy about `AnyAccessor` at all is avoided here: the literal `[any]` key
            // is the structural arm's business, not the expansion arm's.
            if (accessor == ANY_ACCESSOR_IDX) return@forEachEntry
            if (!manager.isCoveredByAny(accessor)) return@forEachEntry

            child.collectNodesContainsAnyAccessor(pattern, nodes)
        }
    }

    fun allNodes(): Sequence<S> {
        val storages = mutableListOf<S>()

        val unprocessedStorages = mutableListOf(this)
        while (unprocessedStorages.isNotEmpty()) {
            val storage = unprocessedStorages.removeLast()
            @Suppress("UNCHECKED_CAST")
            storages.add(storage as S)

            storage.children.forEachEntry { _, s ->
                if (s == null) return@forEachEntry
                unprocessedStorages.add(s)
            }
        }

        return storages.asSequence()
    }

    fun forEachNode(body: (AccessPath.AccessNode?, S) -> Unit) {
        forEachNodeWithAccessorChain { accessors, s ->
            val ap = manager.createNodeFromAccessors(accessors)
            body(ap, s)
        }
    }

    fun forEachNodeWithAccessorChain(body: (IntArrayList, S) -> Unit) {
        val unprocessedStorages = mutableListOf(IntArrayList() to this)
        while (unprocessedStorages.isNotEmpty()) {
            val (accessors, storage) = unprocessedStorages.removeLast()

            @Suppress("UNCHECKED_CAST")
            body(accessors, storage as S)

            storage.children.forEachEntry { accessor, s ->
                if (s == null) return@forEachEntry

                val childrenAccessors = accessors.clone()
                childrenAccessors.add(accessor)

                unprocessedStorages.add(childrenAccessors to s)
            }
        }
    }

    fun removeChildren(predicate: (AccessorIdx, S) -> Boolean) {
        val accessorsToRemove = IntArrayList()

        children.forEachEntry { accessor, s ->
            if (s == null) return@forEachEntry

            if (predicate(accessor, s)) {
                accessorsToRemove.add(accessor)
            }
        }

        if (accessorsToRemove.isEmpty) return

        accessorsToRemove.forEachInt { accessor ->
            children.put(accessor, null)
        }
    }

    open fun getOrCreateChild(accessor: AccessorIdx): S =
        children.getOrCreateNullable(accessor) { createStorage() }

    open fun findChild(accessor: AccessorIdx): S? =
        children.get(accessor)

    override fun toString(): String = buildString {
        print(this, prefix = "")
    }

    abstract fun printStorageNode(): String

    fun print(builder: StringBuilder, prefix: String) {
        builder.appendLine("$prefix${printStorageNode()}")
        children.forEachEntry { accessorIdx, s ->
            if (s == null) return@forEachEntry
            val accessor = with(manager) { accessorIdx.accessor }
            builder.appendLine("$prefix$accessor ->")
            s.print(builder, prefix + " ".repeat(4))
        }
    }
}

/**
 * Insertion-ordered, identity-deduplicating sink for [AccessBasedStorage.filterContains].
 *
 * `collectNodesContains` adds the current node at every level and the `[any]` rule reaches the same
 * node both through the pattern and through an expansion step, so the walk genuinely produces
 * repeats; before this, they became duplicate `FactToFact` edges. Dedup is by identity, which is
 * exact here -- a trie node is a unique object at a unique key path.
 *
 * Results are almost always tiny, so a linear identity scan beats hashing until the list grows past
 * [LINEAR_SCAN_LIMIT], at which point it switches to a map and stays O(1) per add. It never becomes
 * an O(n^2) walk.
 */
class ContainsNodeCollector<S : Any> {
    private val nodes = mutableListOf<S>()
    private var seen: IdentityHashMap<S, Unit>? = null

    fun add(node: S) {
        if (!markSeen(node)) return
        nodes.add(node)
    }

    fun asSequence(): Sequence<S> = nodes.asSequence()

    /** @return `true` when [node] had not been collected before. */
    private fun markSeen(node: S): Boolean {
        seen?.let { return it.put(node, Unit) == null }

        for (i in nodes.indices) {
            if (nodes[i] === node) return false
        }

        if (nodes.size >= LINEAR_SCAN_LIMIT) {
            val known = IdentityHashMap<S, Unit>()
            nodes.forEach { known.put(it, Unit) }
            known.put(node, Unit)
            seen = known
        }

        return true
    }

    private companion object {
        const val LINEAR_SCAN_LIMIT = 8
    }
}
