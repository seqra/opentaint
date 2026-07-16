package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class KkFileViewSetterIdentityRegressionTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"

    @Test
    fun `tainted whole local survives unrelated setters and reaches sink through field getter`() {
        val testClass = "test.samples.KkFileViewSetterIdentityRegressionSample"
        val ruleId = "kkfileview-setter-identity-regression"
        val mark = "kkfileview-untrusted-path"
        val config = SerializedTaintConfig(
            source = listOf(sourceRule(testClass, "source", mark)),
            sink = listOf(sinkRule(testClass, "sink", ruleId, listOf(Argument(0) to mark)))
        )

        assertReachable(
            config = config,
            testCls = testClass,
            entryPointName = "taintedLocalSurvivesUnrelatedSetters",
            ruleId = ruleId,
            testName = "kkFileView setter identity Tree control",
            apMode = ApMode.Tree,
        )

        assertReachable(
            config = config,
            testCls = testClass,
            entryPointName = "taintedLocalSurvivesUnrelatedSetters",
            ruleId = ruleId,
            testName = "kkFileView setter identity BaseOnly regression",
            apMode = ApMode.BaseOnlyField,
        )
    }
}
