package org.opentaint.dataflow.bidi.store

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.walkPath
import org.opentaint.dataflow.util.Cancellation

/** Single-writer positional index. A value at two positions remains two entries. */
class PathTrie<V : Any>(private val cancellation: Cancellation? = null) {
    private class Node<V : Any> {
        val values = LinkedHashSet<V>(2)
        var children: Int2ObjectOpenHashMap<Node<V>>? = null
        fun child(accessor: Int): Node<V>? = children?.get(accessor)
        fun getOrCreate(accessor: Int): Node<V> {
            val map = children ?: Int2ObjectOpenHashMap<Node<V>>().also { children = it }
            return map.getOrPut(accessor) { Node() }
        }
    }
    private val roots = HashMap<AccessPathBase, Node<V>>(4)

    fun add(base: AccessPathBase, path: IntArray, value: V): Boolean {
        cancellation?.checkpoint()
        var node = roots.getOrPut(base) { Node() }
        for (accessor in path) {
            cancellation?.checkpoint()
            node = node.getOrCreate(accessor)
        }
        return node.values.add(value)
    }

    val isEmpty: Boolean get() = roots.isEmpty()

    /** Remove one exact posting and release its now-empty path. No retained
     * historical key remains after the owner removes its last relation. */
    fun remove(base: AccessPathBase, path: IntArray, value: V): Boolean {
        cancellation?.checkpoint()
        val root = roots[base] ?: return false
        val parents = ArrayList<Node<V>>(path.size)
        var node = root
        for (accessor in path) {
            cancellation?.checkpoint()
            parents += node
            node = node.child(accessor) ?: return false
        }
        cancellation?.checkpoint()
        if (!node.values.remove(value)) return false
        // Finish pruning without another cancellable operation after mutation.
        for (i in path.indices.reversed()) {
            if (node.values.isNotEmpty() || node.children?.isNotEmpty() == true) break
            val parent = parents[i]
            parent.children?.remove(path[i])
            if (parent.children?.isEmpty() == true) parent.children = null
            node = parent
        }
        if (root.values.isEmpty() && root.children == null) roots.remove(base)
        return true
    }

    fun lookupPrefixes(base: AccessPathBase, path: IntArray): MutableList<V> {
        cancellation?.checkpoint()
        val out = ArrayList<V>()
        val root = roots[base] ?: return out
        walkPath(root, path, Node<V>::child) { _, node ->
            cancellation?.checkpoint()
            out += node.values
        }?.let { out += it.values }
        return out
    }

    fun lookupExtensions(base: AccessPathBase, path: IntArray): List<V> {
        cancellation?.checkpoint()
        val out = ArrayList<V>()
        find(base, path)?.let { collect(it, out, self = true) }
        return out
    }

    fun around(base: AccessPathBase, path: IntArray): List<V> =
        lookupPrefixes(base, path).also { out -> find(base, path)?.let { collect(it, out, self = false) } }

    /** Finite owner-local visit; the callback must not mutate this index or its owning directory. */
    fun visitAround(base: AccessPathBase, path: IntArray, visit: (V) -> Unit) {
        visitAroundWhile(base, path) { visit(it); true }
    }

    /** A read-only query can stop at its first witness without allocating a candidate list. */
    fun visitAroundWhile(base: AccessPathBase, path: IntArray, visit: (V) -> Boolean): Boolean {
        cancellation?.checkpoint()
        var node = roots[base] ?: return true
        fun values(at: Node<V>): Boolean {
            for (value in at.values) {
                cancellation?.checkpoint()
                if (!visit(value)) return false
            }
            return true
        }
        for (accessor in path) {
            cancellation?.checkpoint()
            if (!values(node)) return false
            node = node.child(accessor) ?: return true
        }
        val stack = ArrayDeque<Node<V>>()
        stack.addLast(node)
        while (stack.isNotEmpty()) {
            cancellation?.checkpoint()
            val at = stack.removeLast()
            if (!values(at)) return false
            at.children?.values?.forEach {
                cancellation?.checkpoint()
                stack.addLast(it)
            }
        }
        return true
    }

    fun all(): Sequence<V> = sequence {
        cancellation?.checkpoint()
        for (root in roots.values) {
            val out = ArrayList<V>()
            collect(root, out, self = true)
            for (value in out) {
                cancellation?.checkpoint()
                yield(value)
            }
        }
    }

    private fun find(base: AccessPathBase, path: IntArray): Node<V>? {
        cancellation?.checkpoint()
        return roots[base]?.let { root ->
            walkPath(root, path, Node<V>::child) { _, _ -> cancellation?.checkpoint() }
        }
    }

    private fun collect(node: Node<V>, out: MutableList<V>, self: Boolean) {
        cancellation?.checkpoint()
        val stack = ArrayDeque<Node<V>>()
        if (self) out += node.values
        node.children?.values?.let(stack::addAll)
        while (stack.isNotEmpty()) {
            cancellation?.checkpoint()
            val next = stack.removeLast()
            out += next.values
            next.children?.values?.let(stack::addAll)
        }
    }
}
