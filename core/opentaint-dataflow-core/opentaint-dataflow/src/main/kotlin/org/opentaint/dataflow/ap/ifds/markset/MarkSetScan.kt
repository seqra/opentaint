package org.opentaint.dataflow.ap.ifds.markset

import java.util.BitSet

/**
 * The flow-insensitive mark-set scan (spec §6.1–§6.5), on the method graph:
 * nodes are methods, so `U(n) = U(method n)`.
 *
 * It computes, for the mark-set program:
 * - `S_E` per root (`InS`, with the joined and sinkGen corrections);
 * - the applicable sites (`Applicable`, via `applicable_iff_union`);
 * - the needed marks (`Needed`).
 *
 * The outputs are checked against the proven Lean reference by oracle tests.
 */
object MarkSetScan {
    private const val CANCEL_CHECK_PERIOD = 4096

    fun run(
        p: MarkSetProgram,
        options: MarkSetOptions = MarkSetOptions(),
        checkCancelled: () -> Unit = {},
    ): MarkSetResult = Scan(p, options, checkCancelled).run()

    /** A deduplicated site signature: `(cond, gens, kind == SINK)`. */
    private data class SigKey(val cond: MarkCond, val gens: List<Int>, val isSink: Boolean)

    private class Sig(val cond: MarkCond, val gens: BitSet, val isSink: Boolean) {
        val atoms: BitSet = cond.atoms()
        val hasJoinedCube: Boolean = cond.hasJoinedCube()
    }

    private class Scan(
        private val p: MarkSetProgram,
        private val options: MarkSetOptions,
        private val checkCancelled: () -> Unit,
    ) {
        private val bitSets = HashMap<BitSet, BitSet>()
        private var closureSteps = 0

        /** Hash-consing: equal sets share one instance, which is never mutated afterwards. */
        private fun intern(set: BitSet): BitSet = bitSets.getOrPut(set) { set }

        private fun step() {
            if (++closureSteps % CANCEL_CHECK_PERIOD == 0) checkCancelled()
        }

        fun run(): MarkSetResult {
            // 1. Condense the methods reachable from the roots.
            val graph = Scc.condense(p.methodCount, p.callees, p.roots)
            val compCount = graph.comps.size

            // 2. Signatures.
            val sigIds = HashMap<SigKey, Int>()
            val sigs = mutableListOf<Sig>()
            val siteSig = IntArray(p.sites.size)
            for ((i, site) in p.sites.withIndex()) {
                val key = SigKey(site.cond, site.gens.toList(), site.kind == SiteKind.SINK)
                siteSig[i] = sigIds.getOrPut(key) {
                    val gens = BitSet().apply { site.gens.forEach { set(it) } }
                    sigs += Sig(site.cond, gens, key.isSink)
                    sigs.size - 1
                }
            }

            val local = Array(compCount) { BitSet() }
            for ((i, site) in p.sites.withIndex()) {
                val c = graph.compOf[site.method]
                if (c >= 0) local[c].set(siteSig[i])
            }
            // Bottom-up: successors have smaller component indices.
            val sigOf = arrayOfNulls<BitSet>(compCount)
            for (c in 0 until compCount) {
                val set = local[c]
                for (s in graph.compSucc[c]) set.or(sigOf[s]!!)
                sigOf[c] = intern(set)
            }

            // The sites the joined/sinkGen pass must test: with gens, reachable, and
            // either a sink or holding a joined cube (a non-sink without one never fires).
            val passSites = p.sites.indices.filter { i ->
                val site = p.sites[i]
                val sig = sigs[siteSig[i]]
                site.gens.isNotEmpty() && graph.compOf[site.method] >= 0 && (sig.isSink || sig.hasJoinedCube)
            }

            val forced = arrayOfNulls<BitSet>(p.methodCount)
            val reachableRoots = p.roots.filter { graph.compOf[it] >= 0 }
            val rootsOfComp = HashMap<Int, MutableList<Int>>()
            for (root in reachableRoots) rootsOfComp.getOrPut(graph.compOf[root]) { mutableListOf() } += root

            val closures = HashMap<Pair<BitSet, BitSet>, BitSet>()
            var rootMarks: Map<Int, BitSet>
            var unions: Array<BitSet?>
            var outerRounds = 0

            while (true) {
                checkCancelled()
                outerRounds++

                // 3. Forced marks, bottom-up.
                val xr = arrayOfNulls<BitSet>(compCount)
                for (c in 0 until compCount) {
                    val set = BitSet()
                    for (m in graph.comps[c]) forced[m]?.let { set.or(it) }
                    for (s in graph.compSucc[c]) set.or(xr[s]!!)
                    xr[c] = intern(set)
                }

                // 4. Per root, the closure over its signatures, seeded by its forced marks.
                rootMarks = LinkedHashMap()
                for (root in reachableRoots) {
                    val c = graph.compOf[root]
                    val sigSet = sigOf[c]!!
                    val seed = xr[c]!!
                    rootMarks[root] = closures.getOrPut(sigSet to seed) { closure(sigs, sigSet, seed) }
                }

                // 5. Unions, top-down: callers have larger component indices.
                unions = arrayOfNulls(compCount)
                val acc = arrayOfNulls<BitSet>(compCount)
                for (c in compCount - 1 downTo 0) {
                    val set = acc[c] ?: BitSet()
                    rootsOfComp[c]?.forEach { set.or(rootMarks.getValue(it)) }
                    val u = intern(set)
                    unions[c] = u
                    acc[c] = null
                    for (s in graph.compSucc[c]) {
                        val target = acc[s] ?: BitSet().also { acc[s] = it }
                        target.or(u)
                    }
                }

                // 6. Joined and sinkGen pass.
                var changed = false
                for (i in passSites) {
                    val site = p.sites[i]
                    val sig = sigs[siteSig[i]]
                    val u = unions[graph.compOf[site.method]]!!
                    val x = forced[site.method]
                    if (x != null && containsAll(x, sig.gens)) continue
                    step()
                    val eval = sig.cond.eval(u)
                    val fires = (if (sig.isSink) eval.sat else eval.big) || relaxedJoined(sig, u)
                    if (!fires) continue
                    val target = x ?: BitSet().also { forced[site.method] = it }
                    target.or(sig.gens)
                    changed = true
                }
                if (!changed) break
            }

            // 7. Applicability.
            val applicable = BitSet()
            var applicableSinks = 0
            for ((i, site) in p.sites.withIndex()) {
                val c = graph.compOf[site.method]
                if (c < 0) continue
                val u = unions[c]!!
                val sig = sigs[siteSig[i]]
                step()
                if (sig.cond.eval(u).sat || relaxedJoined(sig, u)) {
                    applicable.set(i)
                    if (site.kind == SiteKind.SINK) applicableSinks++
                }
            }

            // 8. Relevance.
            val needed = if (options.relevance) {
                needed(sigs, siteSig, applicable)
            } else {
                BitSet().apply { set(0, p.markCount) }
            }

            val stats = MarkSetStats(
                methods = p.methodCount,
                edges = p.callees.sumOf { it.size },
                sites = p.sites.size,
                signatures = sigs.size,
                distinctRootSets = rootMarks.values.distinctBy { System.identityHashCode(it) }.size,
                outerRounds = outerRounds,
                applicableSites = applicable.cardinality(),
                applicableSinks = applicableSinks,
                neededMarks = needed.cardinality(),
            )
            return MarkSetResult(applicable, needed, rootMarks, stats)
        }

        /** Option 4*: a joined cube holds when some atom of the condition is in [u]. */
        private fun relaxedJoined(sig: Sig, u: BitSet): Boolean =
            options.relaxed && sig.hasJoinedCube && sig.atoms.intersects(u)

        /**
         * `closure(sig, xr)`: start from [seed], then add the gens of every
         * signature whose condition has a satisfied cube of at most one literal,
         * until nothing changes.
         */
        private fun closure(sigs: List<Sig>, sigSet: BitSet, seed: BitSet): BitSet {
            val marks = seed.clone() as BitSet
            val done = BitSet()
            var changed = true
            while (changed) {
                changed = false
                var s = sigSet.nextSetBit(0)
                while (s >= 0) {
                    if (!done.get(s)) {
                        val sig = sigs[s]
                        step()
                        if (sig.cond.eval(marks).smallSat) {
                            done.set(s)
                            if (!containsAll(marks, sig.gens)) {
                                marks.or(sig.gens)
                                changed = true
                            }
                        }
                    }
                    s = sigSet.nextSetBit(s + 1)
                }
            }
            return intern(marks)
        }

        /** The least fixpoint of spec §6.3, over applicable signatures. */
        private fun needed(sigs: List<Sig>, siteSig: IntArray, applicable: BitSet): BitSet {
            val needed = p.cleanerAtoms.clone() as BitSet
            val appSigs = BitSet()
            var i = applicable.nextSetBit(0)
            while (i >= 0) {
                val sig = sigs[siteSig[i]]
                appSigs.set(siteSig[i])
                when (p.sites[i].kind) {
                    SiteKind.SINK -> {
                        needed.or(sig.atoms)
                        needed.or(sig.gens)
                    }
                    SiteKind.PASS_THROUGH -> needed.or(sig.atoms)
                    SiteKind.SOURCE -> Unit
                }
                i = applicable.nextSetBit(i + 1)
            }

            val done = BitSet()
            var changed = true
            while (changed) {
                changed = false
                var s = appSigs.nextSetBit(0)
                while (s >= 0) {
                    if (!done.get(s)) {
                        val sig = sigs[s]
                        if (sig.gens.intersects(needed)) {
                            done.set(s)
                            if (!containsAll(needed, sig.atoms)) {
                                needed.or(sig.atoms)
                                changed = true
                            }
                        }
                    }
                    s = appSigs.nextSetBit(s + 1)
                }
            }
            return needed
        }

        private fun containsAll(set: BitSet, subset: BitSet): Boolean {
            var m = subset.nextSetBit(0)
            while (m >= 0) {
                if (!set.get(m)) return false
                m = subset.nextSetBit(m + 1)
            }
            return true
        }
    }
}
