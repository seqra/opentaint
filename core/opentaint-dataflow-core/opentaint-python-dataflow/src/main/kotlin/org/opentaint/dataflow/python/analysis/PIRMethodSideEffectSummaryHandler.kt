package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.taint.MethodSideEffectHandlerWithAnyAccessorRequestHandling

/**
 * No-op side effect handler for the minimal prototype.
 * All methods use default implementations from MethodSideEffectSummaryHandler.
 */
class PIRMethodSideEffectSummaryHandler(
    override val runner: AnalysisRunner
) : MethodSideEffectHandlerWithAnyAccessorRequestHandling
