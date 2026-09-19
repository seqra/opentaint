package org.opentaint.dataflow.ap.ifds

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicLong

/**
 * WHICH METHOD explodes.
 *
 * Every OOM and every timeout in this work has been attributed to aggregate counters -- total facts,
 * total nodes, events per second. None of them names a method, so no configuration could ever be
 * explained, only ranked. This census answers the only question that makes a configuration
 * intelligible: **which methods hold the facts, and does that set change when the configuration
 * changes?**
 *
 * `MethodAnalyzerEdges.add` is the choke point: one instance exists per `MethodEntryPoint`, and every
 * edge for that method passes through it. Counting there gives, per method:
 *
 * * `offered` -- edges arriving;
 * * `accepted` -- edges that were new and produced successor edges, which is what actually grows;
 * * `contexts` -- distinct `MethodEntryPoint`s for the same method, i.e. how far the method is
 *   re-analysed under different contexts.
 *
 * The key is the method WITHOUT its context, because the question is which code explodes, not which
 * context did. Contexts are counted separately so that context blow-up is visible as its own column.
 *
 * Off unless `-Dopentaint.methodCensus=true`, and the hot path is one `enabled` read when off.
 */
object MethodFactCensus {
    /** A fact this long is what the census calls DEEP. Median is 13, p99 is 40. */
    const val DEEP = 40

    private val HOP_MARKERS = arrayOf(".MapValue", ".MapKey", ".Element", ".Value", ".Entry")

    /** How many times this path steps through a container abstraction. */
    fun countHops(path: String): Int {
        var n = 0
        for (m in HOP_MARKERS) {
            var i = path.indexOf(m)
            while (i >= 0) { n++; i = path.indexOf(m, i + 1) }
        }
        return n
    }

    val enabled: Boolean =
        System.getProperty("opentaint.methodCensus")?.toBooleanStrictOrNull() ?: false

    private class Counts {
        val offered = AtomicLong()
        val accepted = AtomicLong()
        val contexts = ConcurrentHashMap.newKeySet<String>()
        /** Access-path SIZE of each accepted fact, bucketed 0..8+. Deep chains vs many shallow facts. */
        val sizeHist = Array(41) { AtomicLong() }
        /** Distinct bases the method's facts are rooted at -- breadth of the fact population. */
        val bases = ConcurrentHashMap.newKeySet<String>()
        val abstractFacts = AtomicLong()
        val maxSize = AtomicLong()
        /** For DEEP facts: is the long path made of FEW repeated accessors (a cycle) or many distinct ones? */
        val deepFacts = AtomicLong()
        val deepDistinctSum = AtomicLong()
        val deepSizeSum = AtomicLong()
        val samples = ConcurrentHashMap.newKeySet<String>()
        /** EXCLUSIONS: an axis `size` cannot see. Do many facts share one path and differ only here? */
        val distinctPaths = ConcurrentHashMap.newKeySet<String>()
        val distinctFacts = ConcurrentHashMap.newKeySet<String>()
        val exclSizeSum = AtomicLong()
        val exclCount = AtomicLong()
        val exclMax = AtomicLong()
        /** WHICH accessors build the deep paths: application fields, or library internals? */
        val deepAccessors = ConcurrentHashMap<String, AtomicLong>()
        /**
         * Distinct accessors over ALL facts, not just deep ones.
         *
         * The type filter is what stops a fact admitting every field. On an `Object`-typed value it
         * has no type to filter against and admits all of them, so a method whose receiver is an
         * ERASED GENERIC should show far higher accessor diversity than one with a concrete type.
         * That is the difference between "the fan-out is TYPE-driven" and "path-driven", and path
         * retention has already been refuted twice (report section 22).
         */
        val allAccessors = ConcurrentHashMap.newKeySet<String>()
        /**
         * Distinct EDGE TRIPLES `(initial, statement, final)`.
         *
         * An IFDS edge is a triple; `distinctFacts` counts only the FINAL. Dividing accepted edges
         * by distinct finals therefore compares two different units and says nothing about
         * re-derivation (report section 29). THIS is the denominator that does: accepted / distinct
         * triples near 1 means every accepted edge was new work; a large ratio means the same triple
         * is processed repeatedly.
         */
        val distinctEdges = ConcurrentHashMap.newKeySet<String>()
        /**
         * COLLECTION HOPS per fact: how many times the path steps THROUGH a container abstraction
         * (`Map#MapValue`, `Iterable#Element`, ...). Total depth has no exploitable gap (section 9),
         * but nesting DEPTH THROUGH CONTAINERS may: a real flow needs one or two, and the payload-map
         * recursion needs many.
         */
        val hopHist = Array(16) { AtomicLong() }
        val statements = ConcurrentHashMap.newKeySet<String>()
    }

    private val byMethod = ConcurrentHashMap<String, Counts>()

    /**
     * Methods to report REGARDLESS of rank, as a comma-separated substring list.
     *
     * The top-N view answers "what explodes". Localising a LOST FINDING needs the opposite: the
     * methods on the flow are small and never enter the top 40, so their disappearance under a bound
     * is invisible. Watch them by name and compare bounded against unbounded.
     */
    private val watch: List<String> =
        (System.getProperty("opentaint.methodCensusWatch") ?: "")
            .split(',').map { it.trim() }.filter { it.isNotEmpty() }

    fun record(method: String, context: String, accepted: Int) {
        if (!enabled) return
        val c = byMethod.computeIfAbsent(method) { Counts() }
        c.offered.incrementAndGet()
        if (accepted > 0) c.accepted.addAndGet(accepted.toLong())
        c.contexts.add(context)
    }

    /** The SHAPE of one accepted fact, so the explosion can be attributed to depth or to breadth. */
    fun recordShape(
        method: String, statement: String, base: String, size: Int, isAbstract: Boolean,
        distinctAccessors: Int = -1, sample: String? = null,
        pathKey: String? = null, factKey: String? = null, exclSize: Int = -1,
        accessorNames: Collection<String>? = null, collectionHops: Int = -1,
        edgeKey: String? = null
    ) {
        if (!enabled) return
        val c = byMethod.computeIfAbsent(method) { Counts() }
        if (size >= DEEP && distinctAccessors >= 0) {
            c.deepFacts.incrementAndGet()
            c.deepDistinctSum.addAndGet(distinctAccessors.toLong())
            c.deepSizeSum.addAndGet(size.toLong())
            if (sample != null && c.samples.size < 3) c.samples.add(sample.take(400))
            if (accessorNames != null && c.deepAccessors.size < 5000) {
                for (a in accessorNames) {
                    c.deepAccessors.computeIfAbsent(a) { AtomicLong() }.incrementAndGet()
                }
            }
        }
        c.sizeHist[size.coerceIn(0, 40)].incrementAndGet()
        c.maxSize.updateAndGet { prev -> if (size > prev) size.toLong() else prev }
        c.bases.add(base)
        c.statements.add(statement)
        if (isAbstract) c.abstractFacts.incrementAndGet()
        if (collectionHops >= 0) c.hopHist[collectionHops.coerceIn(0, 15)].incrementAndGet()
        if (pathKey != null && c.distinctPaths.size < 200_000) c.distinctPaths.add(pathKey)
        if (accessorNames != null && c.allAccessors.size < 20_000) c.allAccessors.addAll(accessorNames)
        if (factKey != null && c.distinctFacts.size < 200_000) c.distinctFacts.add(factKey)
        if (edgeKey != null && c.distinctEdges.size < 400_000) c.distinctEdges.add(edgeKey)
        if (exclSize >= 0) {
            c.exclCount.incrementAndGet()
            c.exclSizeSum.addAndGet(exclSize.toLong())
            c.exclMax.updateAndGet { prev -> if (exclSize > prev) exclSize.toLong() else prev }
        }
    }

    /** The top methods by ACCEPTED edges -- the ones that actually grow. */
    fun report(topN: Int = 40): String {
        if (!enabled) return "methodCensus=off"
        val rows = byMethod.entries
            .map { (m, c) -> Row(m, c.offered.get(), c.accepted.get(), c.contexts.size) }
            .sortedByDescending { it.accepted }
        val totalAcc = rows.sumOf { it.accepted }
        val totalOff = rows.sumOf { it.offered }
        val sb = StringBuilder()
        sb.append("METHODCENSUS methods=").append(rows.size)
            .append(" offered=").append(totalOff)
            .append(" accepted=").append(totalAcc).append('\n')
        sb.append("  METHODROW accepted offered contexts acc_share method\n")
        for (r in rows.take(topN)) {
            val share = if (totalAcc > 0) 100.0 * r.accepted / totalAcc else 0.0
            sb.append("  METHODROW ").append(r.accepted).append(' ')
                .append(r.offered).append(' ').append(r.contexts).append(' ')
                .append(String.format("%.2f", share)).append(" ").append(r.method).append('\n')
        }
        // SHAPE of the top methods: what the facts in them actually look like.
        // The accessors that BUILD the deep paths, pooled across the top methods.
        val pooled = HashMap<String, Long>()
        for (r in rows.take(8)) {
            val c = byMethod[r.method] ?: continue
            for ((a, n) in c.deepAccessors) pooled.merge(a, n.get(), Long::plus)
        }
        sb.append("  HOPHDR method hops[0..15]\n")
        for (r in rows.take(8)) {
            val c = byMethod[r.method] ?: continue
            sb.append("  HOPS ")
            for (i in 0..15) sb.append(c.hopHist[i].get()).append(if (i == 15) ' ' else ',')
            sb.append(r.method).append('\n')
        }
        sb.append("  DEEPACCHDR count accessor\n")
        for ((a, n) in pooled.entries.sortedByDescending { it.value }.take(25)) {
            sb.append("  DEEPACC ").append(n).append(' ').append(a).append('\n')
        }
        sb.append("  EXCLHDR method distinctPaths distinctFacts factsPerPath avgExcl maxExcl\n")
        for (r in rows.take(8)) {
            val c = byMethod[r.method] ?: continue
            val paths = c.distinctPaths.size
            val facts = c.distinctFacts.size
            val n = c.exclCount.get()
            sb.append("  EXCL ").append(paths).append(' ').append(facts).append(' ')
                .append(String.format("%.2f", if (paths > 0) facts.toDouble() / paths else 0.0)).append(' ')
                .append(String.format("%.1f", if (n > 0) c.exclSizeSum.get().toDouble() / n else 0.0)).append(' ')
                .append(c.exclMax.get()).append(' ').append(r.method).append('\n')
        }
        sb.append("  CYCLEHDR method deepFacts avgSize avgDistinct ratio\n")
        for (r in rows.take(8)) {
            val c = byMethod[r.method] ?: continue
            val n = c.deepFacts.get()
            if (n == 0L) continue
            val avgSize = c.deepSizeSum.get().toDouble() / n
            val avgDist = c.deepDistinctSum.get().toDouble() / n
            sb.append("  CYCLE ").append(n).append(' ')
                .append(String.format("%.1f", avgSize)).append(' ')
                .append(String.format("%.1f", avgDist)).append(' ')
                .append(String.format("%.2f", avgSize / avgDist)).append(' ')
                .append(r.method).append('\n')
            for (sm in c.samples) sb.append("  CYCLESAMPLE ").append(sm).append('\n')
        }
        sb.append("  SHAPEHDR method stmts bases abstract maxsize sizes[0..40]\n")
        for (r in rows.take(12)) {
            val c = byMethod[r.method] ?: continue
            sb.append("  METHODSHAPE ").append(c.statements.size).append(' ')
                .append(c.bases.size).append(' ').append(c.abstractFacts.get()).append(' ')
                .append(c.maxSize.get()).append(' ')
            for (i in 0..40) sb.append(c.sizeHist[i].get()).append(if (i == 40) ' ' else ',')
            sb.append(r.method).append('\n')
        }
        if (watch.isNotEmpty()) {
            sb.append("  WATCHHDR accepted offered contexts distinctAccessors distinctEdges method\n")
            for (r in rows) {
                if (watch.none { r.method.contains(it) }) continue
                val c = byMethod[r.method]
                sb.append("  WATCH ").append(r.accepted).append(' ')
                    .append(r.offered).append(' ').append(r.contexts).append(' ')
                    .append(c?.allAccessors?.size ?: 0).append(' ')
                    .append(c?.distinctEdges?.size ?: 0).append(' ')
                    .append(r.method).append('\n')
            }
        }
        return sb.toString()
    }

    private class Row(val method: String, val offered: Long, val accepted: Long, val contexts: Int)
}
