package org.opentaint.dataflow.ap.ifds.markset

import kotlinx.serialization.json.Json
import kotlinx.serialization.json.JsonArray
import kotlinx.serialization.json.JsonObject
import kotlinx.serialization.json.boolean
import kotlinx.serialization.json.int
import kotlinx.serialization.json.jsonArray
import kotlinx.serialization.json.jsonObject
import kotlinx.serialization.json.jsonPrimitive
import java.util.BitSet
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * Layer 1 of the spec's test plan (§8): the Kotlin scan against the proven Lean
 * reference functions (`refInS`, `refApplicable`, `refNeeded`), on the seeded
 * random programs of `formal/markset-scan/Oracle.lean`.
 *
 * Regenerate the fixture with
 * `cd formal/markset-scan && lake exe markset-oracle 400 1 > <this module>/src/test/resources/markset/oracle.json`.
 */
class MarkSetScanOracleTest {
    private class OracleCase(
        val seed: Int,
        val program: MarkSetProgram,
        val inS: Map<Int, Set<Int>>,
        val applicable: Set<Int>,
        val needed: Set<Int>,
    )

    private val cases: List<OracleCase> by lazy { loadCases() }

    @Test
    fun `the fixture has programs`() {
        assertTrue(cases.size >= 400, "expected at least 400 oracle programs, got ${cases.size}")
    }

    @Test
    fun `exact mode matches the Lean reference on every program`() {
        val failures = mutableListOf<String>()
        for (case in cases) {
            val result = MarkSetScan.run(case.program)

            for (root in case.program.roots) {
                val actual = result.rootMarks[root]?.toSet() ?: emptySet()
                val expected = case.inS[root] ?: emptySet()
                if (actual != expected) {
                    failures += "seed ${case.seed}: S_E of root $root = $actual, expected $expected"
                }
            }
            val applicable = result.applicable.toSet()
            if (applicable != case.applicable) {
                failures += "seed ${case.seed}: applicable = $applicable, expected ${case.applicable}"
            }
            val needed = result.needed.toSet()
            if (needed != case.needed) {
                failures += "seed ${case.seed}: needed = $needed, expected ${case.needed}"
            }
        }
        if (failures.isNotEmpty()) {
            fail("${failures.size} mismatches:\n" + failures.take(20).joinToString("\n"))
        }
    }

    @Test
    fun `option 4-star over-approximates the Lean reference on every program`() {
        val failures = mutableListOf<String>()
        for (case in cases) {
            val result = MarkSetScan.run(case.program, MarkSetOptions(relaxed = true))

            val applicable = result.applicable.toSet()
            if (!applicable.containsAll(case.applicable)) {
                failures += "seed ${case.seed}: relaxed applicable = $applicable misses ${case.applicable - applicable}"
            }
            val needed = result.needed.toSet()
            if (!needed.containsAll(case.needed)) {
                failures += "seed ${case.seed}: relaxed needed = $needed misses ${case.needed - needed}"
            }
        }
        if (failures.isNotEmpty()) {
            fail("${failures.size} mismatches:\n" + failures.take(20).joinToString("\n"))
        }
    }

    @Test
    fun `relevance off makes every mark needed`() {
        for (case in cases) {
            val result = MarkSetScan.run(case.program, MarkSetOptions(relevance = false))
            assertEquals(
                (0 until case.program.markCount).toSet(), result.needed.toSet(),
                "seed ${case.seed}",
            )
            val exact = MarkSetScan.run(case.program)
            assertEquals(exact.applicable, result.applicable, "seed ${case.seed}: relevance must not change applicability")
        }
    }

    // ---- fixture loading ----------------------------------------------------

    private fun BitSet.toSet(): Set<Int> = stream().toArray().toSet()

    private fun JsonArray.ints(): List<Int> = map { it.jsonPrimitive.int }

    private fun loadCases(): List<OracleCase> {
        val text = javaClass.getResourceAsStream("/markset/oracle.json")
            ?.bufferedReader()?.use { it.readText() }
            ?: error("missing test resource /markset/oracle.json")
        val programs = Json.parseToJsonElement(text).jsonObject.getValue("programs").jsonArray
        return programs.map { toCase(it.jsonObject) }
    }

    private fun toCase(json: JsonObject): OracleCase {
        val nodeCount = json.getValue("nodeCount").jsonPrimitive.int
        val roots = json.getValue("roots").jsonArray.ints()

        val callees = Array(nodeCount) { LinkedHashSet<Int>() }
        for (call in json.getValue("calls").jsonArray) {
            val (caller, _, callee) = call.jsonArray.ints()
            callees[caller] += callee
        }

        var maxMark = -1
        fun seeMark(mark: Int): Int = mark.also { maxMark = maxOf(maxMark, it) }

        val literalIds = hashMapOf<Pair<Int, Int>, Int>()
        fun literalId(base: Int, mark: Int): Int = literalIds.getOrPut(base to mark) { literalIds.size }

        val sites = json.getValue("sites").jsonArray.map { siteJson ->
            val site = siteJson.jsonObject
            val kind = when (val k = site.getValue("kind").jsonPrimitive.content) {
                "source" -> SiteKind.SOURCE
                "sink" -> SiteKind.SINK
                "passThrough" -> SiteKind.PASS_THROUGH
                else -> error("unknown site kind $k")
            }
            val cubes = site.getValue("cond").jsonArray.map { cube ->
                val literals = cube.jsonArray.mapNotNull { litJson ->
                    val lit = litJson.jsonArray
                    val base = lit[0].jsonPrimitive.int
                    val mark = seeMark(lit[1].jsonPrimitive.int)
                    val negated = lit[2].jsonPrimitive.boolean
                    // A negated literal imposes nothing (spec §4.1, E5).
                    if (negated) null else MarkCond.Lit(mark, literalId(base, mark))
                }
                if (literals.isEmpty()) MarkCond.True else MarkCond.And(literals)
            }
            val cond = if (cubes.isEmpty()) MarkCond.False else MarkCond.Or(cubes)
            val gens = site.getValue("gens").jsonArray.ints().map { seeMark(it) }.toIntArray()
            MarkSite(site.getValue("node").jsonPrimitive.int, kind, cond, gens)
        }

        val cleanerAtoms = BitSet()
        for (atom in json.getValue("cleanerAtoms").jsonArray) {
            cleanerAtoms.set(seeMark(atom.jsonArray[2].jsonPrimitive.int))
        }

        val program = MarkSetProgram(
            methodCount = nodeCount,
            markCount = maxMark + 1,
            roots = roots.toIntArray(),
            callees = Array(nodeCount) { callees[it].toIntArray() },
            sites = sites,
            cleanerAtoms = cleanerAtoms,
        )

        val expected = json.getValue("expected").jsonObject
        val inS = hashMapOf<Int, MutableSet<Int>>()
        for (pair in expected.getValue("inS").jsonArray) {
            val (root, mark) = pair.jsonArray.ints()
            inS.getOrPut(root) { hashSetOf() } += mark
        }

        return OracleCase(
            seed = json.getValue("seed").jsonPrimitive.int,
            program = program,
            inS = inS,
            applicable = expected.getValue("applicable").jsonArray.ints().toSet(),
            needed = expected.getValue("needed").jsonArray.ints().toSet(),
        )
    }
}
