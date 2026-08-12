package org.opentaint.semgrep.pattern.diff.structure

import org.opentaint.semgrep.pattern.Formula
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.SemgrepTraceEntry
import org.opentaint.semgrep.pattern.convertToRawRule
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals

class FormulaDnfCubeTest {
    private fun trace() = SemgrepRuleLoadStepTrace(SemgrepTraceEntry.Step.BUILD_CONVERT_TO_RAW_RULE)

    @Test
    fun `cube extraction agrees with normal raw conversion`() {
        val formula = Formula.And(
            listOf(
                Formula.Or(listOf(Formula.LeafPattern("a()"), Formula.LeafPattern("b()"))),
                Formula.LeafPattern("c()"),
            )
        )

        val cubes = formulaToDnfCubes(formula, trace())

        assertEquals(convertToRawRule(formula, trace()), cubes.map { it.raw })
        assertEquals(listOf(0, 1), cubes.map { it.ordinal })
        assertEquals(listOf(listOf("a()", "c()"), listOf("b()", "c()")), cubes.map { it.key.patterns })
    }

    @Test
    fun `canonical key ignores conjunction order and retains multiplicity`() {
        val first = Formula.And(
            listOf(
                Formula.LeafPattern("b()"),
                Formula.LeafPattern("a()"),
                Formula.LeafPattern("a()"),
            )
        )
        val reordered = Formula.And(
            listOf(
                Formula.LeafPattern("a()"),
                Formula.LeafPattern("b()"),
                Formula.LeafPattern("a()"),
            )
        )

        val firstKey = formulaToDnfCubes(first, trace()).single().key
        val reorderedKey = formulaToDnfCubes(reordered, trace()).single().key

        assertEquals(firstKey, reorderedKey)
        assertEquals(listOf("a()", "a()", "b()"), firstKey.patterns)
    }

    @Test
    fun `metavariable names are not alpha normalized`() {
        val x = Formula.And(listOf(Formula.LeafPattern("value()"), Formula.MetavarFocus("\$X")))
        val y = Formula.And(listOf(Formula.LeafPattern("value()"), Formula.MetavarFocus("\$Y")))

        assertNotEquals(
            formulaToDnfCubes(x, trace()).single().key,
            formulaToDnfCubes(y, trace()).single().key,
        )
    }
}
