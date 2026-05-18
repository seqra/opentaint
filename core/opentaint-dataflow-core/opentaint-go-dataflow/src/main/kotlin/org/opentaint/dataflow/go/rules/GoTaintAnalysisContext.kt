package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.configuration.CommonTaintRulesProvider

class GoTaintAnalysisContext(
    override val taintSinkTracker: TaintSinkTracker,
    val taintConfig: GoTaintRulesProvider,
): TaintAnalysisContext
