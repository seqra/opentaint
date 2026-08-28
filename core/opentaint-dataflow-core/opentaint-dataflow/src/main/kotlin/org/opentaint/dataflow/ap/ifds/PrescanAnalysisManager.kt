package org.opentaint.dataflow.ap.ifds

import org.opentaint.ir.api.common.CommonMethod

interface PrescanAnalysisManager : TaintAnalysisManager {
    fun startPrescan(
        scopeMethods: Collection<CommonMethod>,
        manager: AnalysisUnitRunnerManager,
    )

    fun finishPrescan()
}
