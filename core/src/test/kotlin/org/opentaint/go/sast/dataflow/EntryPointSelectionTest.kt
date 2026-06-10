package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.go.sast.project.filterEntryPoints
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class EntryPointSelectionTest : AnalysisTest() {

    private fun allEntryPoints() =
        cp.packages.values.filter { it.isProject }
            .flatMap { it.functions }
            .filter { it.hasBody && !it.isSynthetic && it.parent == null }

    @Test fun nullSelectorReturnsAll() {
        val all = allEntryPoints()
        assertEquals(all.toSet(), filterEntryPoints(all, null).toSet())
    }

    @Test fun starSelectorReturnsAll() {
        val all = allEntryPoints()
        assertEquals(all.toSet(), filterEntryPoints(all, "*").toSet())
    }

    @Test fun fullNameSelectorReturnsExactlyOne() {
        val all = allEntryPoints()
        val target = all.first { it.fullName == "test.sample" }
        assertEquals(listOf(target), filterEntryPoints(all, "test.sample"))
    }

    @Test fun unknownNameSelectorReturnsEmpty() {
        val all = allEntryPoints()
        assertTrue(filterEntryPoints(all, "test.doesNotExist").isEmpty())
    }
}
