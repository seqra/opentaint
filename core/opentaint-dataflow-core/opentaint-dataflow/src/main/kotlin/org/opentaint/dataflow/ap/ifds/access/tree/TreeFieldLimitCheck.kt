package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import java.util.IdentityHashMap
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.ThreadLocalRandom
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.LongAccumulator
import java.util.concurrent.atomic.LongAdder

/** Diagnostic verifier of [TreeApManager.fieldLimit], reported once at JVM exit. */
@JvmField
internal val TREE_FIELD_LIMIT_CHECK: Boolean = System.getProperty("opentaint.treeFieldLimitCheck").toBoolean()

internal object TreeFieldLimitCheck {
    const val PREPEND = 0
    const val CONCAT = 1
    const val OTHER = 2

    private const val SAMPLE_RATE = 256
    private const val MAX_EXAMPLES = 5
    private const val EXAMPLE_LENGTH = 500

    @Volatile
    private var limit = -1

    private val finalChecked = LongAdder()
    private val finalViolations = LongAdder()
    private val finalMaxDepth = LongAccumulator(::maxOf, 0)
    private val sampled = LongAdder()
    private val sampleMismatch = LongAdder()
    private val sampleViolations = LongAdder()
    private val initialChecked = LongAdder()
    private val initialViolations = LongAdder()
    private val initialMaxDepth = LongAccumulator(::maxOf, 0)
    private val truncations = Array(3) { LongAdder() }

    private val exampleCount = AtomicInteger()
    private val examples = ConcurrentLinkedQueue<String>()

    init {
        Runtime.getRuntime().addShutdownHook(Thread({ report().forEach(::println) }, "tree-field-limit-report"))
    }

    fun checkFinal(tree: AccessTree) {
        val manager = tree.apManager
        val fieldLimit = manager.fieldLimit
        limit = fieldLimit

        val depth = tree.access.boundedDepth
        finalChecked.increment()
        finalMaxDepth.accumulate(depth.toLong())

        var violation = depth > fieldLimit

        if (ThreadLocalRandom.current().nextInt(SAMPLE_RATE) == 0) {
            sampled.increment()
            val recomputed = countedDepth(manager, tree.access, IdentityHashMap())
            if (recomputed != depth) sampleMismatch.increment()
            if (recomputed > fieldLimit) {
                sampleViolations.increment()
                violation = true
            }
        }

        if (!violation) return
        finalViolations.increment()

        if (exampleCount.getAndIncrement() < MAX_EXAMPLES) {
            examples.add(tree.toString().take(EXAMPLE_LENGTH).replace('\n', ' '))
        }
    }

    fun checkInitial(manager: TreeApManager, path: AccessPath) {
        val fieldLimit = manager.fieldLimit
        limit = fieldLimit

        var depth = 0
        var node: AccessPath.AccessNode? = path.access
        while (node != null) {
            if (isCountedIndependent(manager, node.accessor)) depth++
            node = node.next
        }

        initialChecked.increment()
        initialMaxDepth.accumulate(depth.toLong())
        if (depth > fieldLimit) initialViolations.increment()
    }

    fun truncated(site: Int) {
        truncations[site].increment()
    }

    // Independent of AccessNode.boundedDepth and of the manager's cache
    private fun countedDepth(
        manager: TreeApManager,
        node: AccessTree.AccessNode,
        cache: IdentityHashMap<AccessTree.AccessNode, Int>,
    ): Int {
        cache[node]?.let { return it }

        var depth = 0
        node.forEachAccessor { accessor, child ->
            var childDepth = countedDepth(manager, child, cache)
            if (isCountedIndependent(manager, accessor)) childDepth++
            if (childDepth > depth) depth = childDepth
        }

        cache[node] = depth
        return depth
    }

    private fun isCountedIndependent(manager: TreeApManager, accessor: AccessorIdx): Boolean =
        (accessor.isFieldAccessor() || accessor == ELEMENT_ACCESSOR_IDX) && manager.isCoveredByAny(accessor)

    private fun report(): List<String> {
        val header = buildString {
            append("TREELIMIT limit=$limit")
            append(" final.checked=${finalChecked.sum()}")
            append(" final.violations=${finalViolations.sum()}")
            append(" final.maxDepth=${finalMaxDepth.get()}")
            append(" sampled=${sampled.sum()}")
            append(" sampleMismatch=${sampleMismatch.sum()}")
            append(" sampleViolations=${sampleViolations.sum()}")
            append(" initial.checked=${initialChecked.sum()}")
            append(" initial.violations=${initialViolations.sum()}")
            append(" initial.maxDepth=${initialMaxDepth.get()}")
            append(" trunc.prepend=${truncations[PREPEND].sum()}")
            append(" trunc.concat=${truncations[CONCAT].sum()}")
            append(" trunc.other=${truncations[OTHER].sum()}")
        }
        return listOf(header) + examples.map { "TREELIMIT example: $it" }
    }
}
