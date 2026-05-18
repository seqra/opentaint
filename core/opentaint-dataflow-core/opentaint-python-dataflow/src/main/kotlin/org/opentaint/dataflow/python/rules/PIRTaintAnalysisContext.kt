package org.opentaint.dataflow.python.rules

import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.configuration.CommonTaintRulesProvider

class PIRTaintAnalysisContext(
    override val taintSinkTracker: TaintSinkTracker,
    val taintConfig: PIRTaintConfig,
): TaintAnalysisContext
