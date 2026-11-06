package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import java.util.EnumMap
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * The concrete fuzz test (IMPL §9.1 item 4, design §10.1 L1 step 6).
 *
 * For each seeded [RandomAliasProgram], the engine runs one time, and its states must pass the
 * post-fixpoint check (an A4-violating program can only fail the empty-cell condition). Then [ConcreteExecutor] runs
 * random executions of the same CFG (callees write new objects or new nulls into reached cells,
 * A2; a catch gives an unknown exception, A6). At each configuration (node `v` and the concrete
 * state before it), for each two paths `r1.p1`, `r2.p2` (`r` a live local, `this` or an argument;
 * at most two cells) with the same value instance, the engine state before `v` must give a
 * may-alias (a common origin). Each reached node must have an engine state.
 *
 * Count: [PROGRAMS] programs from [BASE_SEED], [RUNS] runs of at most [STEPS] steps each (about
 * 20 s). The system property `opentaint.test.concreteFuzzPrograms` changes the count.
 *
 * The locals that are not live at `v` are not checked: the engine removes them (IMPL §5.3), and
 * no later read sees their values (`csoundKill`).
 */
class ConcreteFuzzTest {

    @Test
    fun `each value alias of a random execution is a may-alias of the engine`() {
        val count = Integer.getInteger(COUNT_PROPERTY, PROGRAMS)
        var configurations = 0L
        var aliases = 0L
        val start = System.nanoTime()
        ends.clear()
        for (i in 0 until count) {
            val seed = BASE_SEED + i
            val program = RandomAliasProgram(seed)
            try {
                val (c, a) = fuzz(program)
                configurations += c
                aliases += a
            } catch (e: Throwable) {
                throw AssertionError("Seed $seed: ${e.message}\n${program.text()}", e)
            }
        }
        val ms = (System.nanoTime() - start) / 1_000_000
        println("Concrete fuzz: $count programs, $RUNS runs each, $configurations configurations, $aliases checked alias pairs, run ends $ends, $ms ms")
        assertTrue(aliases > count, "too few checked aliases: $aliases")
    }

    private val ends = EnumMap<ConcreteExecutor.End, Int>(ConcreteExecutor.End::class.java)

    private fun fuzz(p: RandomAliasProgram): Pair<Long, Long> {
        val transfer = AliasTransfer(p.tables)
        val states = solveChecked(p, DirectedFixpoint(transfer))
        val nodes = p.tables.nodes
        val rnd = Random(p.seed * 31 + 7)
        val roots = listOf<AliasValue.Ref>(AliasValue.This, AliasValue.Arg(0), AliasValue.Arg(1)) +
            p.locals.map { AliasValue.Local(it) }
        val abstract = HashMap<Triple<Int, AliasValue.Ref, List<CellId>>, IntArray>()
        var configurations = 0L
        var aliases = 0L

        fun origins(v: Int, st: AliasState, r: AliasValue.Ref, cells: List<CellId>): IntArray =
            abstract.getOrPut(Triple(v, r, cells)) {
                var n = transfer.valueNode(st, r)
                for (c in cells) n = transfer.load(st, n, c)
                nodes.members(n)
            }

        repeat(RUNS) {
            val exec = ConcreteExecutor(p.cfg, p.tables, rnd)
            val paths = paths(exec.checkCells)
            val end = exec.run(STEPS) { v, cst ->
                configurations++
                val est = states.statesBefore[v] ?: fail("an execution reaches node $v; the engine has no state there")
                val live = p.cfg.liveIn(v)
                val groups = HashMap<ConcreteExecutor.Value, MutableList<Pair<AliasValue.Ref, List<ConcreteExecutor.CCell>>>>()
                for (r in roots) {
                    if (r is AliasValue.Local && !live.get(r.v)) continue
                    val start = exec.rootValue(r, cst) ?: continue
                    for (path in paths) {
                        val value = read(cst, start, path) ?: continue
                        groups.getOrPut(value) { ArrayList() } += r to path
                    }
                }
                for (group in groups.values) {
                    if (group.size < 2) continue
                    for (i in group.indices) for (j in i + 1 until group.size) {
                        val (r1, p1) = group[i]
                        val (r2, p2) = group[j]
                        val a = origins(v, est, r1, p1.map { it.cell })
                        val b = origins(v, est, r2, p2.map { it.cell })
                        aliases++
                        if (a.none { b.contains(it) }) {
                            fail(
                                "node $v: ${show(r1, p1)} and ${show(r2, p2)} are the same value " +
                                    "${cst.let { read(it, exec.rootValue(r1, it)!!, p1) }}, but the engine gives " +
                                    "${a.toList()} and ${b.toList()}",
                            )
                        }
                    }
                }
            }
            ends.merge(end, 1, Int::plus)
        }
        return configurations to aliases
    }

    /**
     * Runs the engine and checks the post-fixpoint conditions. A program that can read an unassigned
     * local (A4 fails) can only fail the empty-cell condition.
     */
    private fun solveChecked(p: RandomAliasProgram, fixpoint: DirectedFixpoint): FixpointStates {
        val states = fixpoint.solve(p.cfg)
        val violations = PostFixChecker(fixpoint).check(p.cfg, states)
        if (p.assignedPrefix || violations.any { "holds the empty set" !in it }) {
            assertEquals(emptyList(), violations, "post-fixpoint check")
        }
        return states
    }

    private fun read(st: ConcreteExecutor.State, start: ConcreteExecutor.Value, path: List<ConcreteExecutor.CCell>): ConcreteExecutor.Value? {
        var v = start
        for (c in path) {
            val o = (v as? ConcreteExecutor.Value.O)?.obj ?: return null
            v = st.cell(o, c)
        }
        return v
    }

    private fun paths(cells: List<ConcreteExecutor.CCell>): List<List<ConcreteExecutor.CCell>> {
        val out = ArrayList<List<ConcreteExecutor.CCell>>()
        out += emptyList<ConcreteExecutor.CCell>()
        for (a in cells) {
            out += listOf(a)
            for (b in cells) out += listOf(a, b)
        }
        return out
    }

    private fun show(r: AliasValue.Ref, p: List<ConcreteExecutor.CCell>): String =
        r.toString() + p.joinToString("") { if (it.cell == ELEM_CELL) "[${it.index}]" else ".c${it.cell}" }

    private companion object {
        const val COUNT_PROPERTY = "opentaint.test.concreteFuzzPrograms"
        const val PROGRAMS = 4000
        const val RUNS = 30
        const val STEPS = 80
        const val BASE_SEED = 7_000_000L
    }
}
