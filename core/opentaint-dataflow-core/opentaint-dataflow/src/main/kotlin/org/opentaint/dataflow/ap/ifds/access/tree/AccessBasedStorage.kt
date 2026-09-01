package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.createNodeFromAccessors
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.util.ConcurrentReadSafeInt2ObjectMap
import org.opentaint.dataflow.util.forEachEntry
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.dataflow.util.getOrCreateNullable
import org.opentaint.dataflow.util.int2ObjectMap

abstract class AccessBasedStorage<S : AccessBasedStorage<S>>(
    val manager: TreeApManager
) {
    private class SingleChild(
        @JvmField val accessor: AccessorIdx,
        @JvmField val storage: Any,
    )

    @Volatile
    private var children: Any? = null

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
            findChild(FINAL_ACCESSOR_IDX)?.let { nodes.add(it) }
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
        findChild(accessor)?.collectNodesContains(pattern, nodes)
    }

    fun allNodes(): Sequence<S> {
        val storages = mutableListOf<S>()

        val unprocessedStorages = mutableListOf(this)
        while (unprocessedStorages.isNotEmpty()) {
            val storage = unprocessedStorages.removeLast()
            @Suppress("UNCHECKED_CAST")
            storages.add(storage as S)

            storage.forEachChild { _, s ->
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

            storage.forEachChild { accessor, s ->
                val childrenAccessors = accessors.clone()
                childrenAccessors.add(accessor)

                unprocessedStorages.add(childrenAccessors to s)
            }
        }
    }

    fun removeChildren(predicate: (AccessorIdx, S) -> Boolean) {
        synchronized(this) {
            val current = children ?: return
            if (current is SingleChild) {
                @Suppress("UNCHECKED_CAST")
                val storage = current.storage as S
                if (predicate(current.accessor, storage)) children = null
                return
            }

            @Suppress("UNCHECKED_CAST")
            val map = current as ConcurrentReadSafeInt2ObjectMap<S?>
            val accessorsToRemove = IntArrayList()
            map.forEachEntry { accessor, storage ->
                if (storage != null && predicate(accessor, storage)) {
                    accessorsToRemove.add(accessor)
                }
            }
            accessorsToRemove.forEachInt { accessor -> map.put(accessor, null) }
        }
    }

    open fun getOrCreateChild(accessor: AccessorIdx): S {
        findChild(accessor)?.let { return it }

        synchronized(this) {
            when (val current = children) {
                null -> {
                    val storage = createStorage()
                    children = SingleChild(accessor, storage)
                    return storage
                }

                is SingleChild -> {
                    @Suppress("UNCHECKED_CAST")
                    val currentStorage = current.storage as S
                    if (current.accessor == accessor) return currentStorage

                    val map = int2ObjectMap<S?>()
                    map.put(current.accessor, currentStorage)
                    val storage = createStorage()
                    map.put(accessor, storage)
                    children = map
                    return storage
                }

                else -> {
                    @Suppress("UNCHECKED_CAST")
                    val map = current as ConcurrentReadSafeInt2ObjectMap<S?>
                    return map.getOrCreateNullable(accessor) { createStorage() }
                }
            }
        }
    }

    open fun findChild(accessor: AccessorIdx): S? {
        return when (val current = children) {
            null -> null
            is SingleChild -> {
                if (current.accessor != accessor) return null
                @Suppress("UNCHECKED_CAST")
                current.storage as S
            }
            else -> {
                @Suppress("UNCHECKED_CAST")
                (current as ConcurrentReadSafeInt2ObjectMap<S?>)[accessor]
            }
        }
    }

    private fun forEachChild(body: (AccessorIdx, S) -> Unit) {
        when (val current = children) {
            null -> return
            is SingleChild -> {
                @Suppress("UNCHECKED_CAST")
                body(current.accessor, current.storage as S)
            }
            else -> {
                @Suppress("UNCHECKED_CAST")
                val map = current as ConcurrentReadSafeInt2ObjectMap<S?>
                map.forEachEntry { accessor, storage ->
                    if (storage != null) body(accessor, storage)
                }
            }
        }
    }

    override fun toString(): String = buildString {
        print(this, prefix = "")
    }

    abstract fun printStorageNode(): String

    fun print(builder: StringBuilder, prefix: String) {
        builder.appendLine("$prefix${printStorageNode()}")
        forEachChild { accessorIdx, s ->
            val accessor = with(manager) { accessorIdx.accessor }
            builder.appendLine("$prefix$accessor ->")
            s.print(builder, prefix + " ".repeat(4))
        }
    }
}
