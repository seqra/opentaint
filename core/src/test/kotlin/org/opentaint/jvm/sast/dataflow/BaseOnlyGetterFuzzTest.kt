package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BaseOnlyGetterFuzzTest : AnalysisTest() {
    companion object {
        private const val TEST_CLASS = "test.samples.BaseOnlyGetterFuzzSample"
        private const val TAINT_MARK = "base-only-getter-fuzz"
        private const val RULE_ID = "base-only-getter-fuzz-flow"

        private val CASES = listOf(
            "directGetter",
            "getterIntoLocal",
            "getterWithReassignment",
            "getterThroughIdentity",
            "getterThroughTwoCalls",
            "getterInCallee",
            "getterAndLocalInCallee",
            "getterAfterReceiverAlias",
            "getterAfterTwoReceiverAliases",
            "getterInIfThen",
            "getterAfterIfAssignment",
            "getterInTernary",
            "getterAsTernaryArm",
            "getterInSwitch",
            "getterInForLoop",
            "getterInWhileLoop",
            "getterInDoWhileLoop",
            "getterInTry",
            "getterInSynchronized",
            "nestedGetter",
            "nestedGetterViaLocal",
            "nestedGetterAndValueLocal",
            "nestedGetterThroughIdentity",
            "nestedPublicField",
            "nestedFieldViaLocal",
            "getterReturningFieldViaLocal",
            "getterReturningConditionalField",
            "getterDelegatingToPrivateMethod",
            "inheritedGetter",
            "overriddenGetter",
            "getterFromInterfaceImplementation",
            "getterAfterReceiverIdentity",
            "getterAfterTwoReceiverMethods",
            "getterFromArrayField",
            "getterFromNestedArray",
            "getterStoredInFreshBox",
            "getterStoredBySetter",
            "getterSelectedWithCleanValue",
            "twoGetterCandidates",
        )
    }

    override val sourceFileExtension: String = "java"
    override val useDefaultUnrollStrategy: Boolean = true

    @TestFactory
    fun `Tree finds receiver field flows that BaseOnlyField misses`(): List<DynamicTest> =
        CASES.map { methodName ->
            DynamicTest.dynamicTest(methodName) {
                val config = SerializedTaintConfig(
                    source = listOf(wholeObjectSourceRule(TEST_CLASS, "source", TAINT_MARK)),
                    sink = listOf(sinkRule(TEST_CLASS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
                )

                assertReachable(
                    config = config,
                    testCls = TEST_CLASS,
                    entryPointName = methodName,
                    ruleId = RULE_ID,
                    testName = "$methodName Tree control",
                    apMode = ApMode.Tree,
                )
                assertReachable(
                    config = config,
                    testCls = TEST_CLASS,
                    entryPointName = methodName,
                    ruleId = RULE_ID,
                    testName = "$methodName BaseOnlyField regression",
                    apMode = ApMode.BaseOnlyField,
                )
            }
        }
}
