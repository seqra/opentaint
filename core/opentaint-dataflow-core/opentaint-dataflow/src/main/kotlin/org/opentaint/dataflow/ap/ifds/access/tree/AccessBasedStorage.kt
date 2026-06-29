package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.createNodeFromAccessors
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
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

    fun filterContains(pattern: AccessTree.AccessNode): Sequence<S> {
        val nodes = mutableListOf<S>()
        collectNodesContains(pattern, nodes)
        return nodes.asSequence()
    }

    private fun collectNodesContains(pattern: AccessTree.AccessNode, nodes: MutableList<S>) {
        @Suppress("UNCHECKED_CAST")
        nodes.add(this as S)

        if (pattern.isFinal) {
            children.get(FINAL_ACCESSOR_IDX)?.let { nodes.add(it) }
        }

        pattern.forEachAccessor { accessor, accessorPattern ->
            collectNodesContainsAccessor(accessorPattern, accessor, nodes)
        }
    }

    open fun collectNodesContainsAccessor(
        pattern: AccessTree.AccessNode,
        accessor: AccessorIdx,
        nodes: MutableList<S>
    ) {
        children.get(accessor)?.collectNodesContains(pattern, nodes)
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