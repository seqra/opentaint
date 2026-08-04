package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class BaseOnlyReferenceMutationFuzzTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"

    private val testClass = "test.samples.BaseOnlyReferenceMutationFuzzSample"
    private val ruleId = "baseonly-reference-mutation-fuzz"
    private val mark = "reference-mutation-taint"
    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(testClass, "source", mark)),
        sink = listOf(sinkRule(testClass, "sink", ruleId, listOf(Argument(0) to mark))),
    )

    @TestFactory
    fun `Tree reference flows must also survive BaseOnly summaries`(): List<DynamicTest> =
        samples.map { method ->
            DynamicTest.dynamicTest(method) {
                assertReachable(config, testClass, method, ruleId, "$method Tree control", ApMode.Tree)
                assertReachable(config, testClass, method, ruleId, "$method BaseOnly regression", ApMode.BaseOnlyField)
            }
        }

    private companion object {
        val samples = listOf(
            "holderConstructorAfterTaint",
            "namedHolderConstructorAfterTaint",
            "holderFactoryAfterTaint",
            "namedHolderFactoryAfterTaint",
            "envelopeConstructorAfterTaint",
            "pairConstructorFirstArgument",
            "pairConstructorSecondArgument",
            "assignBoxThroughHolderSetter",
            "holderConstructorAliasArgument",
            "holderConstructorLocalAlias",
            "holderConstructorCastArgument",
            "holderConstructorNullMetadata",
            "holderConstructorIdentityMetadata",
            "tripleConstructorFirstArgument",
            "tripleConstructorMiddleArgument",
            "tripleConstructorLastArgument",
            "tripleFactoryFirstArgument",
            "pairFactoryFirstArgument",
            "pairFactorySecondArgument",
            "holderFactoryAliasedArgument",
            "holderFactoryCastArgument",
            "nestedHolderFactory",
            "doubleEnvelopeConstructor",
            "envelopeWithMetadataConstructor",
            "holderSetterViaHelper",
            "holderSetterWithMetadataViaHelper",
            "holderSetterAliasArgument",
            "holderSetterCastArgument",
            "holderOverwriteSafeThenTainted",
            "holderOverwriteTaintedTwice",
            "alternateHolderPrimaryField",
            "alternateHolderSecondaryField",
            "alternateConstructorPrimaryField",
            "alternateConstructorSecondaryField",
            "alternateOverwritePrimaryField",
            "alternateOverwriteSecondaryField",
            "namedHolderSetBoxAndName",
            "namedHolderSetBoxAndNullName",
            "pairThenEnvelopeFirstField",
            "pairThenEnvelopeSecondField",
            "quadConstructorFirstArgument",
            "quadConstructorSecondArgument",
            "quadConstructorThirdArgument",
            "quadConstructorFourthArgument",
            "quadFactoryFirstArgument",
            "quadFactorySecondArgument",
            "quadFactoryThirdArgument",
            "quadFactoryFourthArgument",
            "keyedConstructorLeftField",
            "keyedConstructorCenterField",
            "keyedConstructorRightField",
            "keyedSetterLeftField",
            "keyedSetterCenterField",
            "keyedSetterRightField",
            "alternatePrimaryViaHelper",
            "alternateSecondaryViaHelper",
            "alternatePrimaryViaNestedHelper",
            "alternatePrimaryViaFactory",
            "alternatePrimaryNullThenTainted",
            "alternateSecondaryNullThenTainted",
            "alternatePrimarySafeThenTaintedViaHelper",
            "holderNullThenTainted",
            "holderTaintedNullThenTainted",
            "quadEnvelopeFirstField",
            "quadEnvelopeFourthField",
            "alternateEnvelopePrimaryField",
            "alternateEnvelopeSecondaryField",
            "alternateSetBothFirstArgument",
            "alternateSetBothSecondArgument",
            "keyedSetAllCenterArgument",
            "quadConstructorFirstWithNullPeers",
            "quadConstructorSecondWithNullPeers",
            "quadConstructorThirdWithNullPeers",
            "quadConstructorFourthWithNullPeers",
            "keyedConstructorLeftWithNullPeers",
            "keyedConstructorCenterWithNullPeers",
            "keyedConstructorRightWithNullPeers",
            "keyedEnvelopeLeftField",
            "keyedEnvelopeCenterField",
            "keyedEnvelopeRightField",
            "doubleAlternateEnvelopePrimaryField",
            "doubleAlternateEnvelopeSecondaryField",
            "keyedOverwriteLeftSafeThenTainted",
            "keyedOverwriteCenterSafeThenTainted",
            "keyedOverwriteRightSafeThenTainted",
            "alternateSetBothFirstWithNullPeer",
            "alternateSetBothSecondWithNullPeer",
            "keyedFactoryLeftField",
            "keyedFactoryCenterField",
            "alternateConstructorPrimaryWithNullPeer",
        )
    }
}
