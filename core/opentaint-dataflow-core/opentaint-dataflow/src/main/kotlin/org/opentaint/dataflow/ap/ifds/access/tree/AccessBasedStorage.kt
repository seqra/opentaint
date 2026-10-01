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

    /**
     * A trie whose keys may contain [any] must enable this (checked once per [filterContains] at the root).
     * Then every node under an [any] key is a candidate for any pattern that reaches the key's parent:
     * an over-approximation, the exact match is done later by [AccessTree.delta].
     */
    protected open val matchesAnyKeys: Boolean get() = false

    fun filterContains(pattern: AccessTree.AccessNode): Sequence<S> {
        val nodes = mutableListOf<S>()
        collectNodesContains(pattern, nodes, matchesAnyKeys)
        return nodes.asSequence()
    }

    private fun collectNodesContains(pattern: AccessTree.AccessNode, nodes: MutableList<S>, anyKeys: Boolean) {
        @Suppress("UNCHECKED_CAST")
        nodes.add(this as S)

        if (anyKeys) {
            children.get(ANY_ACCESSOR_IDX)?.let { nodes += it.allNodes() }
        }

        if (pattern.isFinal) {
            children.get(FINAL_ACCESSOR_IDX)?.let { nodes.add(it) }
        }

        pattern.forEachAccessor { accessor, accessorPattern ->
            collectNodesContainsAccessor(accessorPattern, accessor, nodes, anyKeys)
        }
    }

    open fun collectNodesContainsAccessor(
        pattern: AccessTree.AccessNode,
        accessor: AccessorIdx,
        nodes: MutableList<S>,
        anyKeys: Boolean,
    ) {
        children.get(accessor)?.collectNodesContains(pattern, nodes, anyKeys)
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