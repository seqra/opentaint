package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker

class GoTaintAnalysisContext(
    override val taintSinkTracker: TaintSinkTracker,
    val taintConfig: GoTaintRulesProvider,
    val externalMethodTracker: ExternalMethodTracker? = null,
): TaintAnalysisContext
