package org.opentaint.dataflow.bidi.fixtures

import org.opentaint.dataflow.bidi.driver.HardRunLimitPolicy
import org.opentaint.dataflow.bidi.driver.IncreasingLimits

internal const val TERMINATION_BASELINE_LAST_RUN = 101

/** The production schedule with a test-only last forward barrier. */
internal val TerminationBaselinePolicy = HardRunLimitPolicy(IncreasingLimits, TERMINATION_BASELINE_LAST_RUN)
