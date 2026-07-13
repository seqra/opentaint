package org.opentaint.dataflow.ap.ifds.analysis.alias

class AnalysisResult(
    val manager: AAInfoManager,
    val statesBeforeStmt: Array<ImmutableState?>,
    val statesAfterStmt: Array<ImmutableState?>,
)
