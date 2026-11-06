package org.opentaint.dataflow.jvm.ap.ifds.alias

import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.DirectedMethodStats
import java.util.concurrent.atomic.AtomicLongArray
import java.util.concurrent.atomic.LongAdder

/**
 * The work counters of the directed analysis (IMPL §8; design §11.2). Each directed analysis that
 * ends with a result records its [DirectedMethodStats] one time. A time-out records nothing here
 * (see `group=backend`).
 *
 * Summary line `group=directed`: `methods` (the recorded analyses), then for each counter `<key>Sum`,
 * `<key>P50`, `<key>P99`, `<key>Max` over the methods:
 * - `stmtEvals`: the evaluations of a CFG node (inlined bodies included).
 * - `headIterations`: the iterations of all loop heads of the method. `headIterationsMax`: the most
 *   iterations of one stabilization of one loop.
 * - `nodeCount`: the nodes of the node table. `contentSize`: the sum of their member counts.
 * - `memoHits`, `memoMisses`: the union and rename memo of the node table.
 * - `retires`: the retires that changed a state.
 * - `calls`: the call closures. `callFallbacks`: the closures over `maxCallClosure`.
 * - `inlinedCalls`: the evaluations of an inlined call.
 * - `etreeSize`, `evalSize`: the members of `Etree` and `Eval` at the method exit (the most over the
 *   states; the sets only grow).
 * - `retainedEntries`: the env and heap entries of all stored states of the method.
 * - `fixpointTimeUs`: the time of the fixpoint (with the freeze), in microseconds.
 *
 * Summary line `group=directedCalls`: `calls` (all call closures of the project), and
 * `closureSizeSum`, `closureSizeP50`, `closureSizeP99`, `closureSizeMax`: the size of `R` of one call
 * closure.
 *
 * Summary line `group=directedOrigins`: `symByDepth` (`<depth>:<count>` for each path length 0..K,
 * separated by commas, the `Sym` origins of all methods), `deepOrigins` (the `Deep` origins),
 * `methodsWithDeep` (the methods with a `Deep` origin), `allocChildOrigins` (the `Sym` origins of an
 * `ALLOC_CHILD` base).
 */
class DirectedAliasStats {
    val methods = LongAdder()
    val stmtEvals = StatHistogram()
    val headIterations = StatHistogram()
    val headIterationsMax = StatHistogram()
    val nodeCount = StatHistogram()
    val contentSize = StatHistogram()
    val memoHits = StatHistogram()
    val memoMisses = StatHistogram()
    val retires = StatHistogram()
    val calls = StatHistogram()
    val callFallbacks = StatHistogram()
    val inlinedCalls = StatHistogram()
    val etreeSize = StatHistogram()
    val evalSize = StatHistogram()
    val retainedEntries = StatHistogram()
    val fixpointTimeUs = StatHistogram()

    /** The size of `R` of each call closure. */
    val closureSize = StatHistogram()

    private val symByDepth = AtomicLongArray(MAX_DEPTH + 1)
    val deepOrigins = LongAdder()
    val methodsWithDeep = LongAdder()
    val allocChildOrigins = LongAdder()

    private val distributions: List<Pair<String, StatHistogram>> = listOf(
        "stmtEvals" to stmtEvals,
        "headIterations" to headIterations,
        "headIterationsMax" to headIterationsMax,
        "nodeCount" to nodeCount,
        "contentSize" to contentSize,
        "memoHits" to memoHits,
        "memoMisses" to memoMisses,
        "retires" to retires,
        "calls" to calls,
        "callFallbacks" to callFallbacks,
        "inlinedCalls" to inlinedCalls,
        "etreeSize" to etreeSize,
        "evalSize" to evalSize,
        "retainedEntries" to retainedEntries,
        "fixpointTimeUs" to fixpointTimeUs,
    )

    fun record(m: DirectedMethodStats) {
        methods.increment()
        stmtEvals.record(m.stmtEvals)
        headIterations.record(m.headIterations)
        headIterationsMax.record(m.headIterationsMax)
        nodeCount.record(m.nodeCount)
        contentSize.record(m.contentSize)
        memoHits.record(m.memoHits)
        memoMisses.record(m.memoMisses)
        retires.record(m.retires)
        calls.record(m.calls)
        callFallbacks.record(m.callFallbacks)
        inlinedCalls.record(m.inlinedCalls)
        etreeSize.record(m.etreeSize)
        evalSize.record(m.evalSize)
        retainedEntries.record(m.retainedEntries)
        fixpointTimeUs.record(m.fixpointNanos / 1000)
        for (s in m.closureSizes) closureSize.record(s.toLong())
        for (d in m.symByDepth.indices) {
            val n = m.symByDepth[d]
            if (n != 0L) symByDepth.addAndGet(minOf(d, MAX_DEPTH), n)
        }
        deepOrigins.add(m.deepOrigins)
        if (m.deepOrigins > 0) methodsWithDeep.increment()
        allocChildOrigins.add(m.allocChildOrigins)
    }

    internal fun writeLines(out: MutableList<String>) {
        out += AliasStats.line("directed") {
            put("methods", methods.sum())
            for ((key, h) in distributions) putDistribution(key, h)
        }
        out += AliasStats.line("directedCalls") {
            put("calls", closureSize.count())
            putDistribution("closureSize", closureSize)
        }
        out += AliasStats.line("directedOrigins") {
            var last = 0
            for (d in 0..MAX_DEPTH) if (symByDepth.get(d) != 0L) last = d
            put("symByDepth", (0..last).joinToString(",") { "$it:${symByDepth.get(it)}" })
            put("deepOrigins", deepOrigins.sum())
            put("methodsWithDeep", methodsWithDeep.sum())
            put("allocChildOrigins", allocChildOrigins.sum())
        }
    }

    internal fun reset() {
        methods.reset()
        distributions.forEach { it.second.reset() }
        closureSize.reset()
        for (d in 0..MAX_DEPTH) symByDepth.set(d, 0)
        deepOrigins.reset()
        methodsWithDeep.reset()
        allocChildOrigins.reset()
    }

    private companion object {
        /** The deepest path length with its own counter. A longer path counts here. */
        const val MAX_DEPTH = 63
    }
}
