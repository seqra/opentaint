package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * The Lean vectors of design VS (IMPL §9.1 item 1, design §10.1 layer L0).
 *
 * The resource `lean-vectors.txt` is the output of `formal/directed-alias/Export/Vectors.lean`.
 * `check.sh` of the Lean model regenerates it and fails on a difference. To regenerate it, run
 * `cd formal/directed-alias && lake env lean Export/Vectors.lean > <resource>`. The Lean file
 * documents the line format.
 *
 * Each line runs the engine on its program ([LeanEngineRun]):
 * - `V`: the may-alias answer of the engine (common origin of the two paths, spec §5.2) must be
 *   equal to the Lean answer.
 * - `F`: the engine `findAlias` of the variable (the paths from locals) must hold each `plain`
 *   path and only paths of `paths`. If `plain` and `paths` are equal, the answers are equal. The
 *   two lists differ only by the paths through a deep summary: the engine never follows the self
 *   cells of a deep summary (spec §5.7), and only the depth-K origins of its tables are parents of
 *   a deep summary (ruling of the Task 5 review, `AliasQuery`). The path of the variable itself
 *   is not in the engine answer.
 * - Each run must pass the post-fixpoint check, except the empty-cell condition of a program that
 *   reads a variable that nothing assigns (A4 fails: `siteless_unsound`).
 *
 * Vectors with `eu=0` are skipped: the engine has `entryUnique` on only (D1).
 */
class LeanVectorTest {

    private val vectors: List<LeanVector> by lazy {
        val text = assertNotNull(javaClass.getResource(RESOURCE), "no resource $RESOURCE").readText()
        LeanVectorParser.parseFile(text)
    }

    @TestFactory
    fun `lean vectors`(): List<DynamicTest> = vectors.map { v ->
        DynamicTest.dynamicTest("${v.kind} ${v.name}") {
            assumeTrue(skipReason(v) == null, skipReason(v))
            check(v)
        }
    }

    @Test
    fun `the resource has the vectors of each example file`() {
        val names = vectors.map { it.name.substringBefore('.') }.toSet()
        for (n in EXPECTED_THEOREMS) assertTrue(n in names, "no vector of $n")
        val compared = vectors.count { skipReason(it) == null }
        assertTrue(compared >= 200, "only $compared compared vectors")
        val exactF = vectors.count { it.kind == 'F' && skipReason(it) == null && it.paths == it.plain }
        println(
            "Lean vectors: ${vectors.size} lines (${vectors.count { it.kind == 'V' }} V, " +
                "${vectors.count { it.kind == 'F' }} F); compared $compared; skipped " +
                "${vectors.size - compared} (eu=0); F lines with plain = paths: $exactF",
        )
    }

    private fun skipReason(v: LeanVector): String? =
        if (!v.entryUnique) "eu=0: the engine has entryUnique on only (D1)" else null

    private fun check(v: LeanVector) {
        val run = LeanEngineRun(v)
        val states = run.driver.solve(run.cfg, run.initial, check = false)
        val violations = run.driver.violations(run.cfg, states, run.initial)
        if (violations.isNotEmpty()) {
            val allowed = run.readsUnassigned() && violations.all { "holds the empty set" in it }
            assertTrue(allowed, "post-fixpoint check of ${v.line}:\n" + violations.joinToString("\n"))
        }
        val st = assertNotNull(states.statesBefore[run.queryNode], "no state before node ${run.queryNode}: ${v.line}")
        when (v.kind) {
            'V' -> {
                val (a, b) = v.q!!
                val may = run.driver.may(
                    st, run.local(a.v), a.cells.map(run::cell), run.local(b.v), b.cells.map(run::cell),
                )
                assertEquals(v.may, may, "may-alias of ${v.line}")
            }

            'F' -> {
                val x = v.variable!!
                val vx = run.local(x).v
                val answer = run.driver.query(run.cfg, states).findAlias(run.queryNode, false, PathRoot.Var(vx))
                val engine = assertNotNull(answer).paths
                    .filter { it.root is PathRoot.Var }
                    .map { run.leanPath((it.root as PathRoot.Var).v, it.cells) }
                    .toSet()
                val self = x.toString()
                val upper = v.paths!! - self
                val lower = v.plain!! - self
                if (!upper.containsAll(engine) || !engine.containsAll(lower)) {
                    fail(
                        "findAlias of ${v.line}\n engine: ${engine.sorted()}\n" +
                            " not in Lean: ${(engine - upper).sorted()}\n missing plain: ${(lower - engine).sorted()}",
                    )
                }
            }
        }
    }

    private companion object {
        const val RESOURCE = "lean-vectors.txt"

        /** One theorem of each example file of the exporter. */
        val EXPECTED_THEOREMS = listOf(
            "user_answers", "bo0_cases_VS", "losses_VS", // Sound/ValueSem/Examples.lean
            "answers68", "gapB", "option_answers", // Sound/ValueSem/StaticsExamples.lean
            "bw_needs_distinct_sites", // Sound/ValueSem/BackwardEq.lean
            "o_answersVS", "added_answers", // Opt/ValueSem.lean, Opt/ValueSemCost.lean
            "loopEntry_answers", "nested_answers", "inlined_answer", "guard_answers", // Impl/CfgExamples.lean
            "catchA6_answer", "box_key", // Impl/CfgEngineExamples.lean
        )
    }
}
