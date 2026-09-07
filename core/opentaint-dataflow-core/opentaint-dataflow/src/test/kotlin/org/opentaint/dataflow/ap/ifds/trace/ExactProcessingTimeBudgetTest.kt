package org.opentaint.dataflow.ap.ifds.trace

import org.opentaint.dataflow.util.Cancellation
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.milliseconds

class ExactProcessingTimeBudgetTest {
    @Test
    fun `budget stops an active operation and records its stage`() {
        val budget = ExactProcessingTimeBudget<String>(20.milliseconds)

        val measurement = budget.measure(
            "vulnerability",
            ExactProcessingTimeBudget.Stage.TRACE_RESOLUTION,
            Cancellation(),
        ) { operationCancellation ->
            while (operationCancellation.isActive()) {
                Thread.onSpinWait()
            }
        }

        assertTrue(measurement.snapshot.exhausted)
        assertTrue(measurement.snapshot.traceResolution >= 20.milliseconds)
        assertEquals(0.milliseconds, measurement.snapshot.ruleSearch)
    }

    @Test
    fun `trace and rule stages share one per-key budget`() {
        val budget = ExactProcessingTimeBudget<String>(30.milliseconds)
        val parent = Cancellation()

        budget.measure(
            "first",
            ExactProcessingTimeBudget.Stage.TRACE_RESOLUTION,
            parent,
        ) {
            Thread.sleep(10)
        }
        val measurement = budget.measure(
            "first",
            ExactProcessingTimeBudget.Stage.RULE_SEARCH,
            parent,
        ) { operationCancellation ->
            while (operationCancellation.isActive()) {
                Thread.onSpinWait()
            }
        }

        assertTrue(measurement.snapshot.exhausted)
        assertTrue(measurement.snapshot.traceResolution >= 10.milliseconds)
        assertTrue(measurement.snapshot.ruleSearch.isPositive())
        assertFalse(budget.isExhausted("second"))
    }
}
