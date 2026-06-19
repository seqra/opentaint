package org.opentaint.dataflow.python.rules

import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker

class PIRTaintAnalysisContext(
    override val taintSinkTracker: TaintSinkTracker,
    val taintConfig: PIRTaintRulesProvider,
): TaintAnalysisContext
