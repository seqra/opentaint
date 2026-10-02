package org.opentaint.dataflow.ap.ifds.markset

import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap
import java.util.BitSet

/**
 * Option 3* (spec §9): the flow-sensitive mark-set scan, context-insensitive within a root.
 * It computes `InFS` of `MarkScan/FlowSensitive.lean` on the program's statement graph
 * ([MarkSetProgram.cfg]), with nodes = methods:
 * - per root and per statement, the marks that may hold there, as a fixpoint over the root's
 *   statement graph (never one pass in statement order: `linear_order_unsound`);
 * - marks flow along `succ` with no kills; a call's set flows into the callee's entry; a callee's
 *   exit sets flow to the successors of its calls that the root reaches;
 * - gens of a cube of at most one literal are evaluated on the root's own set at the statement;
 *   gens of a joined cube, and of a sink with any satisfied cube, on the union at the statement
 *   over every root reaching it, and they go to every root reaching it.
 *
 * Then `ApplicableFS` and `NeededOver ApplicableFS` (`MarkScan/Relevance.lean`), which together
 * make the restricted full scan exact (`markset_exact_fs`).
 *
 * Roots are coupled only through the joined and sinkGen placements. Each round runs the affected
 * roots to their fixpoint, one root at a time (so only one root's table is alive), folds their
 * sets into the per-statement unions, and then evaluates the joined and sink sites whose union
 * grew. A root is re-run only when a placement lands in a method it reaches. Within a root, the
 * statements of one strongly connected component share one set, so each component is solved once,
 * in topological order (see [Scan.runRoot]). Mark sets are interned: a statement holds a set id,
 * and unions and transfers are memoized on ids.
 */
object FlowSensitiveScan {
    /** The size guard (spec §9): more `(root, statement)` pairs than this make the phase fail open. */
    const val MAX_ROOT_POINTS: Long = 50_000_000L

    private const val CANCEL_CHECK_PERIOD = 4096
    private const val UNREACHED = -1
    private const val EMPTY = 0
    private const val INITIAL_SLOTS = 1024

    /**
     * The number of `(root, statement)` pairs the scan can visit (Lean `fsPoints_length`, restricted
     * to reachable methods): for every root, the statements of every method it reaches in the call
     * graph. Counting stops as soon as the total exceeds [limit].
     */
    fun rootPoints(p: MarkSetProgram, limit: Long = MAX_ROOT_POINTS): Long {
        val cfg = requireNotNull(p.cfg) { "option 3* needs the statement graph" }
        val stamp = IntArray(p.methodCount) { -1 }
        val stack = IntArray(p.methodCount)
        var total = 0L
        for ((r, root) in p.roots.withIndex()) {
            if (stamp[root] == r) continue
            var top = 0
            stack[top++] = root
            stamp[root] = r
            while (top > 0) {
                val m = stack[--top]
                total += cfg.stmtCount[m]
                if (total > limit) return total
                for (c in p.callees[m]) {
                    if (stamp[c] != r) {
                        stamp[c] = r
                        stack[top++] = c
                    }
                }
            }
        }
        return total
    }

    fun run(
        p: MarkSetProgram,
        options: MarkSetOptions = MarkSetOptions(),
        checkCancelled: () -> Unit = {},
    ): MarkSetResult = Scan(p, options, checkCancelled).run()

    private class Scan(
        private val p: MarkSetProgram,
        private val options: MarkSetOptions,
        private val checkCancelled: () -> Unit,
    ) {
        private val cfg: MethodCfg = requireNotNull(p.cfg) { "option 3* needs the statement graph" }
        private val n = p.methodCount
        private val signatures = Signatures(p)
        private val sigs = signatures.sigs

        /** Global point id of `(m, s)`: `pointBase[m] + s`. */
        private val pointBase = IntArray(n + 1)

        // ---- interned mark sets: id -> set; id 0 is the empty set ------------------
        private val sets = ArrayList<BitSet>()
        private val setIds = HashMap<BitSet, Int>()
        private val unionMemo = Long2IntOpenHashMap().apply { defaultReturnValue(-1) }
        private val transferMemo = Long2IntOpenHashMap().apply { defaultReturnValue(-1) }
        private val sigGensId = IntArray(sigs.size) { -1 }

        // ---- static per-point data ----------------------------------------------
        /** The distinct signatures with gens at a point (the per-root `single` closure). */
        private val genSigsAt: Array<IntArray?>

        /** The sites at a point that the joined/sinkGen pass tests: with gens, and a sink or joined. */
        private val passSitesAt: Array<IntArray?>

        /** For every method, its statements holding a site (where the unions are kept). */
        private val sitePointsOf: Array<IntArray>

        private val isExit = BitSet()

        /** For every callee, its call points `(caller, statement)`, flattened in pairs. */
        private val callSitesOf: Array<IntArray>

        // ---- global state across roots --------------------------------------------
        /** The joined/sinkGen gens placed at a point, for every root reaching it (set id). */
        private val forced: IntArray

        /** The union at a point over every root reaching it (set id); [UNREACHED] if none does. */
        private val pointUnion: IntArray
        private val dirtyUnions = BitSet()

        // ---- the current root's table: its reached methods' statements, as slots ------
        private val base = IntArray(n) { UNREACHED }
        private val touched = IntArrayList()
        private var size = 0
        private var slotMethod = IntArray(INITIAL_SLOTS)

        /** The set at every slot (set id); [UNREACHED] for a statement the root does not reach. */
        private var vals = IntArray(INITIAL_SLOTS)
        private val queue = IntArrayList()

        // The root's supergraph over reached slots (CSR), and its condensation.
        private var edgeStart = IntArray(INITIAL_SLOTS + 1)
        private var edgeTarget = IntArray(INITIAL_SLOTS)
        private var dfsIndex = IntArray(INITIAL_SLOTS)
        private var low = IntArray(INITIAL_SLOTS)
        private var sccOf = IntArray(INITIAL_SLOTS)
        private var tarjanStack = IntArray(INITIAL_SLOTS)
        private var frameSlot = IntArray(INITIAL_SLOTS)
        private var frameEdge = IntArray(INITIAL_SLOTS)

        /** The members of every component, contiguous: component `c` is `members[sccStart[c] until sccStart[c + 1]]`. */
        private var members = IntArray(INITIAL_SLOTS)
        private var sccStart = IntArray(INITIAL_SLOTS + 1)
        private var sccIn = IntArray(INITIAL_SLOTS)
        private val closure = BitSet()

        private var steps = 0
        private var rootPoints = 0L

        init {
            require(cfg.stmtCount.size == n && cfg.succ.size == n && cfg.entry.size == n &&
                cfg.exits.size == n && cfg.callsAt.size == n && cfg.siteStmt.size == p.sites.size) {
                "the statement graph does not match the program"
            }
            for (m in 0 until n) {
                val count = cfg.stmtCount[m]
                require(count >= 1 && cfg.entry[m] in 0 until count) { "method $m has no entry statement" }
                require(cfg.succ[m].size == count && cfg.callsAt[m].size == count) { "method $m: bad statement arrays" }
                require(cfg.exits[m].all { it in 0 until count }) { "method $m: an exit is not a statement" }
                require(cfg.succ[m].all { next -> next.all { it in 0 until count } }) { "method $m: a successor is not a statement" }
                require(cfg.callsAt[m].all { callees -> callees.all { it in 0 until n } }) { "method $m: a callee is not a method" }
                pointBase[m + 1] = Math.addExact(pointBase[m], count)
                for (ex in cfg.exits[m]) isExit.set(pointBase[m] + ex)
            }
            val totalPoints = pointBase[n]
            forced = IntArray(totalPoints)
            pointUnion = IntArray(totalPoints) { UNREACHED }

            sets += BitSet()
            setIds[sets[EMPTY]] = EMPTY

            val genSigs = HashMap<Int, LinkedHashSet<Int>>()
            val passSites = HashMap<Int, IntArrayList>()
            val sitePoints = Array(n) { LinkedHashSet<Int>() }
            for ((i, site) in p.sites.withIndex()) {
                val s = cfg.siteStmt[i]
                require(s in 0 until cfg.stmtCount[site.method]) { "site $i is not at a statement of its method" }
                val gp = pointBase[site.method] + s
                sitePoints[site.method] += s
                if (site.gens.isEmpty()) continue
                val sigId = signatures.siteSig[i]
                genSigs.getOrPut(gp, ::LinkedHashSet) += sigId
                val sig = sigs[sigId]
                if (sig.isSink || sig.hasJoinedCube) passSites.getOrPut(gp, ::IntArrayList).add(i)
            }
            genSigsAt = arrayOfNulls(totalPoints)
            genSigs.forEach { (gp, ids) -> genSigsAt[gp] = ids.toIntArray() }
            passSitesAt = arrayOfNulls(totalPoints)
            passSites.forEach { (gp, ids) -> passSitesAt[gp] = ids.toIntArray() }
            sitePointsOf = Array(n) { sitePoints[it].toIntArray() }

            val callers = Array(n) { IntArrayList() }
            for (m in 0 until n) {
                val calls = cfg.callsAt[m]
                for (s in calls.indices) {
                    for (c in calls[s]) {
                        callers[c].add(m)
                        callers[c].add(s)
                    }
                }
            }
            callSitesOf = Array(n) { callers[it].toIntArray() }
        }

        private fun step() {
            if (++steps % CANCEL_CHECK_PERIOD == 0) checkCancelled()
        }

        fun run(): MarkSetResult {
            val roots = p.roots.distinct()
            val rootReach = arrayOfNulls<BitSet>(roots.size)
            val rootMarks = LinkedHashMap<Int, BitSet>()
            var toRun: List<Int> = roots.indices.toList()
            var rounds = 0

            while (true) {
                checkCancelled()
                rounds++
                for (r in toRun) {
                    val root = roots[r]
                    runRoot(root)
                    rootMarks[root] = rootSet()
                    rootReach[r] = BitSet(n).also { reached -> touched.forEach { reached.set(it) } }
                    foldUnions()
                }

                val placed = placeJoinedAndSinkGens()
                if (placed.isEmpty) break
                transferMemo.clear()
                toRun = roots.indices.filter { rootReach[it]!!.intersects(placed) }
            }

            // ApplicableFS: the statement is reached, and the site's condition holds on the union
            // there (`CubeSatFS`: a small cube on some root's set, a joined cube on the union).
            val applicable = BitSet()
            var applicableSinks = 0
            val satMemo = Long2IntOpenHashMap().apply { defaultReturnValue(-1) }
            for ((i, site) in p.sites.withIndex()) {
                val u = pointUnion[pointBase[site.method] + cfg.siteStmt[i]]
                if (u == UNREACHED) continue
                val sigId = signatures.siteSig[i]
                val key = (sigId.toLong() shl 32) or u.toLong()
                var sat = satMemo.get(key)
                if (sat < 0) {
                    step()
                    val sig = sigs[sigId]
                    val marks = sets[u]
                    sat = if (sig.cond.eval(marks).sat || relaxedJoined(sig, marks)) 1 else 0
                    satMemo.put(key, sat)
                }
                if (sat == 1) {
                    applicable.set(i)
                    if (site.kind == SiteKind.SINK) applicableSinks++
                }
            }

            val needed = if (options.relevance) {
                neededOver(p, signatures, applicable)
            } else {
                BitSet().apply { set(0, p.markCount) }
            }

            val stats = MarkSetStats(
                methods = n,
                edges = p.callees.sumOf { it.size },
                sites = p.sites.size,
                signatures = sigs.size,
                distinctRootSets = rootMarks.values.toHashSet().size,
                outerRounds = rounds,
                applicableSites = applicable.cardinality(),
                applicableSinks = applicableSinks,
                neededMarks = needed.cardinality(),
                rootPoints = rootPoints,
            )
            return MarkSetResult(applicable, needed, rootMarks, stats)
        }

        /** Option 4*: a joined cube holds when some atom of the condition is in [u]. */
        private fun relaxedJoined(sig: Sig, u: BitSet): Boolean =
            options.relaxed && sig.hasJoinedCube && sig.atoms.intersects(u)

        // ---- one root -------------------------------------------------------------

        /**
         * `InFS` for [root], given the current [forced] placements, into [vals].
         *
         * With no kills, the set at a statement is the union over its predecessors in the root's
         * supergraph, closed under the gens at the statement; so every statement of one strongly
         * connected component holds the same set. The run therefore (1) finds the reached statements
         * (`PtReach`: `succ` and call edges), (2) builds the supergraph (`flow`, `callIn`, and `ret`
         * from every exit to the successors of every reached call of its method) and condenses it,
         * and (3) computes one set per component, in topological order, each exactly once.
         */
        private fun runRoot(root: Int) {
            for (i in 0 until touched.size) base[touched.getInt(i)] = UNREACHED
            touched.clear()
            size = 0

            reach(root)
            buildEdges()
            val sccCount = condense(base[root] + cfg.entry[root])
            solve(sccCount)
            rootPoints += size
        }

        /** `PtReach`: allocates the slots of every reached method and marks the reached statements. */
        private fun reach(root: Int) {
            visit(root, cfg.entry[root])
            var head = 0
            while (head < queue.size) {
                val q = queue.getInt(head++)
                step()
                val m = slotMethod[q]
                val s = q - base[m]
                for (t in cfg.succ[m][s]) visit(m, t)
                for (c in cfg.callsAt[m][s]) visit(c, cfg.entry[c])
            }
            queue.clear()
        }

        private fun visit(m: Int, s: Int) {
            var b = base[m]
            if (b == UNREACHED) b = allocate(m)
            val q = b + s
            if (vals[q] != UNREACHED) return
            vals[q] = EMPTY
            queue.add(q)
        }

        private fun allocate(m: Int): Int {
            val b = size
            val end = b + cfg.stmtCount[m]
            if (end > vals.size) grow(maxOf(end, vals.size * 2))
            vals.fill(UNREACHED, b, end)
            slotMethod.fill(m, b, end)
            size = end
            base[m] = b
            touched.add(m)
            return b
        }

        private fun grow(capacity: Int) {
            vals = vals.copyOf(capacity)
            slotMethod = slotMethod.copyOf(capacity)
            edgeStart = IntArray(capacity + 1)
            dfsIndex = IntArray(capacity)
            low = IntArray(capacity)
            sccOf = IntArray(capacity)
            tarjanStack = IntArray(capacity)
            frameSlot = IntArray(capacity)
            frameEdge = IntArray(capacity)
            members = IntArray(capacity)
            sccStart = IntArray(capacity + 1)
            sccIn = IntArray(capacity)
        }

        /** The supergraph's out-edges of every reached slot, in CSR form. */
        private fun buildEdges() {
            var count = 0
            for (q in 0 until size) {
                edgeStart[q] = count
                if (vals[q] != UNREACHED) count += forEachEdge(q) {}
            }
            edgeStart[size] = count
            if (count > edgeTarget.size) edgeTarget = IntArray(maxOf(count, edgeTarget.size * 2))
            var k = 0
            for (q in 0 until size) {
                if (vals[q] != UNREACHED) forEachEdge(q) { edgeTarget[k++] = it }
            }
        }

        /** Calls [body] on every successor slot of the reached slot [q]; returns their number. */
        private inline fun forEachEdge(q: Int, body: (Int) -> Unit): Int {
            val m = slotMethod[q]
            val b = base[m]
            val s = q - b
            var count = 0
            // flow
            for (t in cfg.succ[m][s]) { body(b + t); count++ }
            // callIn
            for (c in cfg.callsAt[m][s]) { body(base[c] + cfg.entry[c]); count++ }
            // ret: from this exit to the successors of every reached call of this method
            if (isExit.get(pointBase[m] + s)) {
                val calls = callSitesOf[m]
                var k = 0
                while (k < calls.size) {
                    val caller = calls[k]
                    val callStmt = calls[k + 1]
                    k += 2
                    val bCaller = base[caller]
                    if (bCaller == UNREACHED || vals[bCaller + callStmt] == UNREACHED) continue
                    for (t in cfg.succ[caller][callStmt]) { body(bCaller + t); count++ }
                }
            }
            return count
        }

        /**
         * Iterative Tarjan from [start], which reaches every reached slot. Components come out in
         * reverse topological order: every edge leaves a component for one with a smaller index.
         */
        private fun condense(start: Int): Int {
            for (q in 0 until size) dfsIndex[q] = UNREACHED
            var nextIndex = 0
            var stackSize = 0
            var sccCount = 0
            var memberCount = 0

            var depth = 0
            frameSlot[0] = start
            frameEdge[0] = edgeStart[start]
            dfsIndex[start] = nextIndex
            low[start] = nextIndex++
            tarjanStack[stackSize++] = start
            sccOf[start] = UNREACHED

            while (depth >= 0) {
                val v = frameSlot[depth]
                val e = frameEdge[depth]
                if (e < edgeStart[v + 1]) {
                    frameEdge[depth] = e + 1
                    val w = edgeTarget[e]
                    if (dfsIndex[w] == UNREACHED) {
                        dfsIndex[w] = nextIndex
                        low[w] = nextIndex++
                        tarjanStack[stackSize++] = w
                        sccOf[w] = UNREACHED
                        depth++
                        frameSlot[depth] = w
                        frameEdge[depth] = edgeStart[w]
                    } else if (sccOf[w] == UNREACHED) {
                        // On the stack: not yet assigned to a component.
                        low[v] = minOf(low[v], dfsIndex[w])
                    }
                    continue
                }

                if (low[v] == dfsIndex[v]) {
                    sccStart[sccCount] = memberCount
                    while (true) {
                        val w = tarjanStack[--stackSize]
                        sccOf[w] = sccCount
                        members[memberCount++] = w
                        if (w == v) break
                    }
                    sccCount++
                }
                depth--
                if (depth >= 0) {
                    val parent = frameSlot[depth]
                    low[parent] = minOf(low[parent], low[v])
                }
            }
            sccStart[sccCount] = memberCount
            return sccCount
        }

        /** One set per component, in topological order; then every reached slot gets its component's set. */
        private fun solve(sccCount: Int) {
            sccIn.fill(EMPTY, 0, sccCount)
            for (c in sccCount - 1 downTo 0) {
                step()
                val set = closeComponent(c, sccIn[c])
                sccIn[c] = set
                for (i in sccStart[c] until sccStart[c + 1]) {
                    val q = members[i]
                    for (e in edgeStart[q] until edgeStart[q + 1]) {
                        val d = sccOf[edgeTarget[e]]
                        if (d != c) sccIn[d] = union(sccIn[d], set)
                    }
                }
            }
            for (q in 0 until size) {
                if (vals[q] != UNREACHED) vals[q] = sccIn[sccOf[q]]
            }
        }

        /**
         * The set of component [c] given its incoming set [inId]: the incoming marks, the placed
         * [forced] gens at its statements, closed under the `single` rule of their sites.
         */
        private fun closeComponent(c: Int, inId: Int): Int {
            val from = sccStart[c]
            val to = sccStart[c + 1]
            if (to - from == 1) return transfer(globalPoint(members[from]), inId)

            var set = inId
            var hasGens = false
            for (i in from until to) {
                val gp = globalPoint(members[i])
                set = union(set, forced[gp])
                if (genSigsAt[gp] != null) hasGens = true
            }
            if (!hasGens) return set

            closure.clear()
            closure.or(sets[set])
            var changed = true
            while (changed) {
                changed = false
                for (i in from until to) {
                    val genSigs = genSigsAt[globalPoint(members[i])] ?: continue
                    if (closeSingles(genSigs)) changed = true
                }
            }
            return intern(closure.clone() as BitSet)
        }

        private fun globalPoint(q: Int): Int {
            val m = slotMethod[q]
            return pointBase[m] + q - base[m]
        }

        /** One pass of the `single` rule over [genSigs] on [closure]; returns whether it grew. */
        private fun closeSingles(genSigs: IntArray): Boolean {
            var grew = false
            for (sigId in genSigs) {
                val sig = sigs[sigId]
                if (closure.containsAll(sig.gens) || !sig.smallSat(closure)) continue
                closure.or(sig.gens)
                grew = true
            }
            return grew
        }

        /**
         * The set at point [gp] given the incoming set [inId]: the incoming marks, the placed
         * [forced] gens, closed under the `single` rule of the point's sites.
         */
        private fun transfer(gp: Int, inId: Int): Int {
            val genSigs = genSigsAt[gp]
            val placed = forced[gp]
            if (genSigs == null) return union(inId, placed)

            val key = (gp.toLong() shl 32) or inId.toLong()
            val memo = transferMemo.get(key)
            if (memo >= 0) return memo

            closure.clear()
            closure.or(sets[inId])
            closure.or(sets[placed])
            while (closeSingles(genSigs)) Unit
            val id = intern(closure.clone() as BitSet)
            transferMemo.put(key, id)
            return id
        }

        // ---- across roots -----------------------------------------------------------

        /** The union of every set of the current root. */
        private fun rootSet(): BitSet {
            val marks = BitSet()
            val seen = BitSet()
            for (q in 0 until size) {
                val v = vals[q]
                if (v <= EMPTY || seen.get(v)) continue
                seen.set(v)
                marks.or(sets[v])
            }
            return marks
        }

        /** Folds the current root's sets at site points into [pointUnion]. */
        private fun foldUnions() {
            for (i in 0 until touched.size) {
                val m = touched.getInt(i)
                val b = base[m]
                for (s in sitePointsOf[m]) {
                    val v = vals[b + s]
                    if (v == UNREACHED) continue
                    val gp = pointBase[m] + s
                    val old = pointUnion[gp]
                    val u = if (old == UNREACHED) v else union(old, v)
                    if (u != old) {
                        pointUnion[gp] = u
                        dirtyUnions.set(gp)
                    }
                }
            }
        }

        /**
         * The joined and sinkGen rules at every point whose union grew: a site whose cube holds on
         * the union places its gens at the point. Returns the methods where a placement grew.
         */
        private fun placeJoinedAndSinkGens(): BitSet {
            val placedIn = BitSet()
            var gp = dirtyUnions.nextSetBit(0)
            while (gp >= 0) {
                val sites = passSitesAt[gp]
                if (sites != null) {
                    val u = sets[pointUnion[gp]]
                    for (i in sites) {
                        val sigId = signatures.siteSig[i]
                        val sig = sigs[sigId]
                        if (sets[forced[gp]].containsAll(sig.gens)) continue
                        step()
                        val eval = sig.cond.eval(u)
                        val fires = (if (sig.isSink) eval.sat else eval.big) || relaxedJoined(sig, u)
                        if (!fires) continue
                        forced[gp] = union(forced[gp], gensId(sigId))
                        placedIn.set(p.sites[i].method)
                    }
                }
                gp = dirtyUnions.nextSetBit(gp + 1)
            }
            dirtyUnions.clear()
            return placedIn
        }

        // ---- interned sets --------------------------------------------------------

        private fun intern(set: BitSet): Int = setIds.getOrPut(set) {
            sets += set
            sets.size - 1
        }

        private fun gensId(sigId: Int): Int {
            var id = sigGensId[sigId]
            if (id < 0) {
                id = intern(sigs[sigId].gens.clone() as BitSet)
                sigGensId[sigId] = id
            }
            return id
        }

        private fun union(a: Int, b: Int): Int {
            if (a == b || b == EMPTY) return a
            if (a == EMPTY) return b
            val key = if (a < b) (a.toLong() shl 32) or b.toLong() else (b.toLong() shl 32) or a.toLong()
            val memo = unionMemo.get(key)
            if (memo >= 0) return memo
            val result = when {
                sets[a].containsAll(sets[b]) -> a
                sets[b].containsAll(sets[a]) -> b
                else -> intern((sets[a].clone() as BitSet).apply { or(sets[b]) })
            }
            unionMemo.put(key, result)
            return result
        }
    }
}
