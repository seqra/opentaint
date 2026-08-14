package org.opentaint.common.sast.dataflow

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.trace.action.ActionableRulesCollectionResult
import kotlin.test.assertEquals
import kotlin.test.assertFalse

class HybridActionableRuleSelectionTest {
    @Test
    fun `does not request fallback when every vulnerability is covered`() {
        var fallbackCalled = false
        val exact = ActionableRulesCollectionResult.Collected(emptyMap())

        val result = actionableRulesWithFallback(listOf(exact, exact)) {
            fallbackCalled = true
            null
        }

        assertEquals(listOf(exact, exact), result)
        assertFalse(fallbackCalled)
    }

    @Test
    fun `keeps exact results and adds one fallback for unprocessed vulnerabilities`() {
        val first = ActionableRulesCollectionResult.Collected(emptyMap())
        val fallback = ActionableRulesCollectionResult.Collected(emptyMap())
        var unprocessedIndices: List<Int>? = null

        val result = actionableRulesWithFallback(
            listOf(
                first,
                ActionableRulesCollectionResult.Unprocessed,
                ActionableRulesCollectionResult.Unprocessed,
            )
        ) { indices ->
            unprocessedIndices = indices
            fallback
        }

        assertEquals(listOf(1, 2), unprocessedIndices)
        assertEquals(listOf(first, fallback), result)
    }

    @Test
    fun `does not fall back for a completed invalid trace`() {
        var fallbackCalled = false

        val result = actionableRulesWithFallback(listOf(ActionableRulesCollectionResult.Failed)) {
            fallbackCalled = true
            ActionableRulesCollectionResult.Collected(emptyMap())
        }

        assertEquals(emptyList(), result)
        assertFalse(fallbackCalled)
    }
}
