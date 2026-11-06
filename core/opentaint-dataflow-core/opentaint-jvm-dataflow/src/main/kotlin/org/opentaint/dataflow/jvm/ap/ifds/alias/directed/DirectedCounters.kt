package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.ints.IntArrayList
import java.util.Collections
import java.util.IdentityHashMap

/**
 * The work counters of one directed analysis (IMPL §8, `DirectedAliasStats`). The fixpoint is
 * single-threaded, so the counters are plain fields. The counters never change a state or an
 * answer.
 */
class DirectedCounters {
    /** The evaluations of a node of an alias CFG (the root CFG and the inlined bodies). */
    var stmtEvals: Long = 0

    /** The iterations of all loops ([WtoComponent.Loop]). */
    var headIterations: Long = 0

    /** The most iterations of one stabilization of one loop. */
    var headIterationsMax: Long = 0

    /** The retires that changed a state (IMPL §4.3). */
    var retires: Long = 0

    /** The call closures (IMPL §4.4): unresolved calls and exceptional edges of calls. */
    var calls: Long = 0

    /** The call closures over the budget `maxCallClosure`. */
    var callFallbacks: Long = 0

    /** The inlined calls (IMPL §5.5): each evaluation of a call node with callee bodies. */
    var inlinedCalls: Long = 0

    /** The size of `R` of each call closure. The closure over the budget gives its size at the stop. */
    val closureSizes = IntArrayList()

    fun recordHeadIterations(n: Long) {
        headIterations += n
        if (n > headIterationsMax) headIterationsMax = n
    }
}

/** The counters of one directed analysis at its end, for `DirectedAliasStats`. */
class DirectedMethodStats(
    val stmtEvals: Long,
    val headIterations: Long,
    val headIterationsMax: Long,
    val nodeCount: Long,
    /** The sum of the member counts of all nodes of the table. */
    val contentSize: Long,
    val memoHits: Long,
    val memoMisses: Long,
    val retires: Long,
    val calls: Long,
    val callFallbacks: Long,
    val inlinedCalls: Long,
    val closureSizes: IntArray,
    /** The most members of `Etree` in a state of the method. The set only grows, so this is its size at the exit. */
    val etreeSize: Long,
    /** The most members of `Eval` in a state of the method. */
    val evalSize: Long,
    /** The env and heap entries of all stored states. A state that two slots share counts one time. */
    val retainedEntries: Long,
    /** The `Sym` origins for each path length 0..K. */
    val symByDepth: LongArray,
    val deepOrigins: Long,
    /** The `Sym` origins of an `ALLOC_CHILD` base. */
    val allocChildOrigins: Long,
    val fixpointNanos: Long,
) {
    companion object {
        /** Reads the counters of [result] and of the tables. It does not change them. */
        fun of(result: DirectedAliasResult, fixpointNanos: Long): DirectedMethodStats {
            val tables = result.tables
            val nodes = tables.nodes
            val counters = tables.counters

            var etree = 0L
            var eval = 0L
            var entries = 0L
            val seen = Collections.newSetFromMap(IdentityHashMap<AliasState, Boolean>())
            for (states in listOf(result.statesBefore, result.statesAfter)) {
                for (st in states) {
                    if (st == null || !seen.add(st)) continue
                    etree = maxOf(etree, nodes.size(st.varNode(ETREE)).toLong())
                    eval = maxOf(eval, nodes.size(st.varNode(EVAL)).toLong())
                    entries += st.env.size + st.heap.size
                }
            }

            val origins = tables.origins
            val symByDepth = LongArray(origins.symDepth + 1)
            var deep = 0L
            var allocChild = 0L
            for (o in 0 until origins.size) {
                when {
                    origins.isSym(o) -> {
                        val d = origins.depth(o)
                        if (d in symByDepth.indices) symByDepth[d]++
                        if (origins.baseKind(o) == BaseKind.ALLOC_CHILD) allocChild++
                    }
                    origins.isDeep(o) -> deep++
                }
            }

            return DirectedMethodStats(
                stmtEvals = counters.stmtEvals,
                headIterations = counters.headIterations,
                headIterationsMax = counters.headIterationsMax,
                nodeCount = nodes.nodeCount.toLong(),
                contentSize = nodes.contentSize,
                memoHits = nodes.memoHits,
                memoMisses = nodes.memoMisses,
                retires = counters.retires,
                calls = counters.calls,
                callFallbacks = counters.callFallbacks,
                inlinedCalls = counters.inlinedCalls,
                closureSizes = counters.closureSizes.toIntArray(),
                etreeSize = etree,
                evalSize = eval,
                retainedEntries = entries,
                symByDepth = symByDepth,
                deepOrigins = deep,
                allocChildOrigins = allocChild,
                fixpointNanos = fixpointNanos,
            )
        }
    }
}
