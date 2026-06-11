package org.opentaint.common.sast.test

import kotlinx.serialization.KSerializer
import org.opentaint.common.sast.CommonAnalysisOptions
import org.opentaint.common.sast.ProjectAnalysisStatus
import org.opentaint.common.sast.ProjectAnalyzerBase
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.project.CommonProject
import kotlin.reflect.KClass

abstract class TestProjectAnalyzerBase<T : TestSampleInfo,
        Ctx : AutoCloseable,
        P : CommonProject,
        Method : CommonMethod,
        Stmt : CommonInst,
        RuleItem, RuleConfig
        >(
    project: P,
    results: ProjectAnalysisTestResults,
    options: CommonAnalysisOptions,
) : ProjectAnalyzerBase<Ctx, P, Method, Stmt, RuleItem, RuleConfig, ProjectAnalysisTestResults>(
    project, results, options
) {
    abstract fun testInfoCls(): KClass<T>
    abstract fun testInfoSerializer(): KSerializer<T>

    abstract fun analyze(): ProjectAnalysisStatus
}
