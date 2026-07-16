package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class BaseOnlyMixedFuzzTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"

    private val testClass = "test.samples.BaseOnlyMixedFuzzSample"
    private val ruleId = "base-only-mixed-fuzz"
    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(testClass, "source", "mixed-fuzz-source")),
        sink = listOf(sinkRule(testClass, "sink", ruleId, listOf(Argument(0) to "mixed-fuzz-source"))),
    )

    private val regressions = listOf(
        "directSetterThenTag", "sourceInLocal", "identityBeforeStore", "identityAfterLoad",
        "aliasBeforeStore", "aliasBeforeMutation", "aliasBeforeLoad", "helperStore", "helperMutation",
        "helperSink", "boxIdentityBeforeStore", "boxIdentityBeforeLoad",
        "fluentStore", "fluentMutation", "fluentChain", "fluentLoad", "doWhileMutation",
        "tryFinallyMutation", "switchMutation", "twoUnrelatedMutations", "primitiveMutation",
        "objectMutation", "nullableMutation", "inheritedMutation", "interfaceDispatchMutation", "supplierSource",
        "loadedIntoLocal", "loadedThroughTwoLocals", "identityTwiceBeforeStore", "identityTwiceAfterLoad",
        "tagBeforeAndAfterStore", "countBeforeTagAfterStore", "helperStoreAndMutation", "helperMutationTwice",
        "fluentStoreHelperMutation", "fluentMutationHelperSink", "twoBoxesFirstTainted", "twoBoxesSecondTainted",
        "synchronizedMutation", "tryCatchMutation", "castBeforeLoad",
    )

    @TestFactory
    fun `Tree findings omitted by BaseOnlyField across mixed codeflow mutations`() = regressions.map { method ->
        DynamicTest.dynamicTest(method) {
            assertReachable(
                config, testClass, method, ruleId, "$method Tree control", ApMode.Tree,
            )
            assertReachable(
                config, testClass, method, ruleId, "$method BaseOnlyField regression", ApMode.BaseOnlyField,
            )
        }
    }
}
