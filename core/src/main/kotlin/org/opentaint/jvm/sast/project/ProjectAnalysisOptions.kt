package org.opentaint.jvm.sast.project

import org.opentaint.common.sast.CommonAnalysisOptions
import org.opentaint.jvm.sast.dataflow.DataFlowApproximationLoader

data class ProjectAnalysisOptions(
    val common: CommonAnalysisOptions = CommonAnalysisOptions(),
    val projectKind: ProjectKind = ProjectKind.UNKNOWN,
    val disableDefaultGetModel: Boolean = false,
    val approximationOptions: DataFlowApproximationLoader.Options = DataFlowApproximationLoader.Options(),
)
