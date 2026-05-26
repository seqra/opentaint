package org.opentaint.go.sast.project

import org.opentaint.jvm.sast.project.CommonAnalysisOptions

data class GoProjectAnalysisOptions(
    val common: CommonAnalysisOptions = CommonAnalysisOptions(),
)
