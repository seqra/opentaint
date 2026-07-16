package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class BaseOnlySetterFuzzTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"

    private val testClass = "test.samples.BaseOnlySetterFuzzSample"
    private val ruleId = "baseonly-setter-fuzz"
    private val mark = "setter-fuzz-taint"
    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(testClass, "source", mark)),
        sink = listOf(sinkRule(testClass, "sink", ruleId, listOf(Argument(0) to mark))),
    )

    @TestFactory
    fun `Tree reaches sink while BaseOnly loses setter identity flows`(): List<DynamicTest> =
        samples.map { method ->
            DynamicTest.dynamicTest(method) {
                assertReachable(
                    config = config,
                    testCls = testClass,
                    entryPointName = method,
                    ruleId = ruleId,
                    testName = "$method Tree control",
                    apMode = ApMode.Tree,
                )
                assertNotReachable(
                    config = config,
                    testCls = testClass,
                    entryPointName = method,
                    testName = "$method BaseOnly regression",
                    apMode = ApMode.BaseOnlyField,
                )
            }
        }

    private companion object {
        val samples = listOf(
            "directUnrelatedStringSetter",
            "sourceLocalThenSetter",
            "sourceThroughIdentity",
            "valueAliasChain",
            "receiverAliasBeforeWrite",
            "receiverAliasForKillingSetter",
            "receiverAliasForRead",
            "distinctAliasesForEveryOperation",
            "castReceiverAtSetter",
            "castReceiverAtGetter",
            "castValueBeforePayloadWrite",
            "factoryAllocatedReceiver",
            "receiverThroughIdentityHelper",
            "payloadWriteThroughHelper",
            "payloadReadThroughHelper",
            "writeAndReadThroughHelpers",
            "twoUnrelatedStringSetters",
            "threeUnrelatedSettersMixedTypes",
            "primitiveSetterKillsIdentity",
            "booleanSetterKillsIdentity",
            "nullMetadataSetter",
            "metadataLocalSetter",
            "metadataIdentitySetter",
            "overwriteMetadataTwice",
            "branchBeforeKillingSetter",
            "bothBranchArmsKillIdentity",
            "branchSelectsSafeMetadata",
            "loopKillingSetter",
            "doWhileKillingSetter",
            "arrayCarriesReceiverAlias",
            "arrayCarriesTaintedValue",
            "holderCarriesReceiverAlias",
            "nestedScopeAliasesReceiver",
            "sinkValueLocalAfterGetter",
            "sinkValueAliasChainAfterGetter",
            "getterResultThroughIdentity",
            "subclassReceiver",
            "interfaceTypedReceiver",
        )
    }
}
