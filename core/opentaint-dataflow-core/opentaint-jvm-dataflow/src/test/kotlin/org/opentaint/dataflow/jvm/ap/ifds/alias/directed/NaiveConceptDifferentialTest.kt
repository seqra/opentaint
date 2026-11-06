package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * The differential test of the engine against [NaiveConcept] (IMPL §9.1 item 2, design §10.1 L1).
 *
 * For each seeded [RandomAliasProgram], the engine ([DirectedFixpoint]) and the naive concept run
 * on the same CFG with the same WTO. For each node the test requires:
 * - the same nodes with a state (before and after the node);
 * - equal states: each local holds the same origins, and each written heap entry holds the same
 *   origins (the normal forms are equal, so the may-alias answers of all paths are equal);
 * - the same strong-update answer (`isUnique`, Lean `uniqueBO`) for each origin of each local;
 * - at the exit and at one more node: equal `findAlias` answers (D = 2) for each local. The naive
 *   answer is the enumeration of the paths whose chain reaches the value of the local, without a
 *   self cell of a deep summary (spec §5.7). The parent of a deep summary through an unwritten
 *   cell must be an origin of the engine tables (ruling of the Task 5 review, `AliasQuery`).
 * - the post-fixpoint check of the engine passes. A program that can read an unassigned local
 *   (A4 fails) can only fail the empty-cell condition.
 *
 * Count: [PROGRAMS] programs (the design target, about 15 s) from [BASE_SEED]. The system
 * property `opentaint.test.naiveConceptPrograms` changes the count.
 */
class NaiveConceptDifferentialTest {

    @Test
    fun `engine states and answers equal the naive concept on random CFGs`() {
        val count = Integer.getInteger(COUNT_PROPERTY, PROGRAMS)
        var nodes = 0
        var queries = 0
        val start = System.nanoTime()
        for (i in 0 until count) {
            val seed = BASE_SEED + i
            val program = RandomAliasProgram(seed)
            try {
                val (n, q) = compare(program)
                nodes += n
                queries += q
            } catch (e: Throwable) {
                throw AssertionError("Seed $seed: ${e.message}\n${program.text()}", e)
            }
        }
        val ms = (System.nanoTime() - start) / 1_000_000
        println("Naive concept differential: $count programs, $nodes compared nodes, $queries findAlias queries, $ms ms")
        assertTrue(nodes > count, "too few compared nodes: $nodes")
    }

    @Test
    fun `naive concept gives the may answers of the Lean vectors of the structured programs`() {
        // A check of the oracle itself: the naive concept is a port of the Lean concept.
        for (line in LeanVectorParser.parseFile(javaClass.getResource("lean-vectors.txt")!!.readText())) {
            if (line.kind != 'V' || !line.entryUnique || line.prog == null) continue
            val run = LeanEngineRun(line)
            val names = NaiveConcept(run.driver.tables, run.cfg, line.k)
            val roots = naiveState(names, run.driver, run.initial).env.values.flatten()
                .map { (it as NaiveConcept.Origin.Sym).base }
            val naive = NaiveConcept(run.driver.tables, run.cfg, line.k, roots)
            val init = naiveState(naive, run.driver, run.initial)
            val st = naive.solve(init).before[run.queryNode] ?: fail("no naive state: ${line.line}")
            val (a, b) = line.q!!
            fun value(p: LPath): Set<NaiveConcept.Origin> {
                var s = st.env[run.local(p.v).v] ?: emptySet()
                for (c in p.cells) s = naive.load(st, s, run.cell(c))
                return s
            }
            assertEquals(line.may, value(a).any { it in value(b) }, "naive may-alias of ${line.line}")
        }
    }

    /** Compares the engine and the naive concept on [p]. It gives the compared nodes and queries. */
    private fun compare(p: RandomAliasProgram): Pair<Int, Int> {
        val transfer = AliasTransfer(p.tables)
        val fixpoint = DirectedFixpoint(transfer)
        val states = fixpoint.solve(p.cfg)
        val violations = PostFixChecker(fixpoint).check(p.cfg, states)
        if (violations.isNotEmpty() && (p.assignedPrefix || violations.any { "holds the empty set" !in it })) {
            fail("post-fixpoint check:\n" + violations.joinToString("\n"))
        }
        val naive = NaiveConcept(p.tables, p.cfg, p.k)
        val result = naive.solve()
        var compared = 0
        for (v in 0 until p.cfg.size) {
            compareState(p, transfer, naive, states.statesBefore[v], result.before[v], "before $v", unique = true)
            compareState(p, transfer, naive, states.statesAfter[v], result.after[v], "after $v", unique = false)
            if (states.statesBefore[v] != null) compared++
        }

        // findAlias at the exit and at one more reached node.
        val tableNames = HashSet<NaiveConcept.Origin>()
        val origins = p.tables.origins
        for (o in 0 until origins.size) if (!origins.isMarker(o)) tableNames += naive.name(origins, o)
        val query = AliasQuery(DirectedAliasResult(p.tables.also { it.freeze() }, p.cfg, states.statesBefore, states.statesAfter), DEPTH)
        val reached = (0 until p.cfg.size).filter { states.statesBefore[it] != null }
        val at = listOf(p.exit) + listOfNotNull(reached.randomOrNull(Random(p.seed)))
        var queries = 0
        for (node in at.distinct()) {
            val nst = result.before[node] ?: continue
            for (x in nst.env.keys) {
                val engine = query.findAlias(node, false, PathRoot.Var(x))!!.paths
                    .filter { it.root is PathRoot.Var }
                    .map { (it.root as PathRoot.Var).v to it.cells }
                    .toSet()
                val expected = naiveFindAlias(naive, nst, x, tableNames, p.tables.cells.size)
                assertEquals(expected, engine, "findAlias of local $x before node $node")
                queries++
            }
        }
        return compared to queries
    }

    private fun compareState(
        p: RandomAliasProgram,
        transfer: AliasTransfer,
        naive: NaiveConcept,
        engine: AliasState?,
        concept: NaiveConcept.State?,
        where: String,
        unique: Boolean,
    ) {
        if (engine == null || concept == null) {
            assertEquals(concept == null, engine == null, "a state $where in only one analysis")
            return
        }
        val origins = p.tables.origins
        val nodes = p.tables.nodes
        val env = HashMap<VarId, Set<NaiveConcept.Origin>>()
        engine.forEachVar { v, n ->
            if (v != ETREE && v != EVAL) env[v] = nodes.members(n).map { naive.name(origins, it) }.toSet()
        }
        assertEquals(concept.env, env, "env $where")
        val heap = HashMap<NaiveConcept.Key, Set<NaiveConcept.Origin>>()
        engine.forEachHeap { key, n ->
            heap[NaiveConcept.Key(naive.name(origins, heapKeyOrigin(key)), heapKeyCell(key))] =
                nodes.members(n).map { naive.name(origins, it) }.toSet()
        }
        assertEquals(concept.heap, heap, "heap $where")
        if (!unique) return
        engine.forEachVar { v, n ->
            if (v == ETREE || v == EVAL) return@forEachVar
            for (o in nodes.members(n)) {
                assertEquals(
                    naive.isUnique(concept, naive.name(origins, o)), transfer.isUnique(engine, o),
                    "isUnique of ${naive.name(origins, o)} $where",
                )
            }
        }
    }

    /**
     * The naive `findAlias(x)`: each local `v` and path `π` (at most [DEPTH] cells) with a chain
     * from the value of `v` along `π` to an origin of `x`, without the path `x` itself. A chain
     * never steps from a deep summary to itself (spec §5.7), and it steps from `⟨b.q⟩` (|q| = K)
     * through an unwritten cell to `deep(b)` only if the engine tables have `⟨b.q⟩`.
     */
    private fun naiveFindAlias(
        naive: NaiveConcept,
        st: NaiveConcept.State,
        x: VarId,
        tableNames: Set<NaiveConcept.Origin>,
        cellCount: Int,
    ): Set<Pair<VarId, List<CellId>>> {
        val seeds = st.env[x] ?: emptySet()
        val cells = (0 until cellCount).toList()
        val out = HashSet<Pair<VarId, List<CellId>>>()
        fun walk(v: VarId, path: List<CellId>, set: Set<NaiveConcept.Origin>) {
            if (set.isEmpty()) return
            if (set.any { it in seeds } && !(v == x && path.isEmpty())) out += v to path
            if (path.size == DEPTH) return
            for (c in cells) {
                val next = HashSet<NaiveConcept.Origin>()
                for (o in set) {
                    val written = st.heap.containsKey(NaiveConcept.Key(o, c))
                    for (o2 in naive.read(st, o, c)) {
                        if (o2 == o && o is NaiveConcept.Origin.Deep) continue
                        if (!written && o2 is NaiveConcept.Origin.Deep && o is NaiveConcept.Origin.Sym && o !in tableNames) continue
                        next += o2
                    }
                }
                walk(v, path + c, next)
            }
        }
        for ((v, s) in st.env) walk(v, emptyList(), s)
        return out
    }

    /** The naive state of an engine state (the initial state of a Lean vector). */
    private fun naiveState(naive: NaiveConcept, driver: DirectedTestDriver, st: AliasState): NaiveConcept.State {
        val env = HashMap<VarId, Set<NaiveConcept.Origin>>()
        st.forEachVar { v, n -> env[v] = driver.nodes.members(n).map { naive.name(driver.origins, it) }.toSet() }
        return NaiveConcept.EMPTY.copy(env = env)
    }

    private companion object {
        const val COUNT_PROPERTY = "opentaint.test.naiveConceptPrograms"
        const val PROGRAMS = 10_000
        const val BASE_SEED = 20_261_106L
        const val DEPTH = 2
    }
}
