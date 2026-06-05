package org.opentaint.go.sast.project

import org.opentaint.common.sast.CommonAnalysisOptions

data class GoProjectAnalysisOptions(
    val common: CommonAnalysisOptions = CommonAnalysisOptions(),
)
