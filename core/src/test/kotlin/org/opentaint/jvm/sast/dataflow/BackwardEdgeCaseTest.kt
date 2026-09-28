package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.ir.api.jvm.ext.cfg.callExpr

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BackwardEdgeCaseTest : AnalysisTest() {

    companion object {
        private const val TEST_CLS = "test.samples.BackwardEdgeCaseSample"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "backward-edge-case-rule"
    }

    override val sourceFileExtension: String = "java"
    override val useDefaultConfig: Boolean = true

    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(TEST_CLS, "source", TAINT_MARK)),
        sink = listOf(sinkRule(TEST_CLS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
    )

    private fun reachable(entryPoint: String) =
        assertReachable(config, TEST_CLS, entryPoint, RULE_ID, entryPoint)

    private fun notReachable(entryPoint: String) =
        assertNotReachable(config, TEST_CLS, entryPoint, entryPoint)

    @Test
    fun `callee allocates a box, stores its parameter into a field and returns it`() = reachable("returnNewBoxField")

    @Test
    fun `callee stores into f, caller reads g`() = notReachable("returnNewBoxOtherField")

    @Test
    fun `field-storing factory reached through a wrapper`() = reachable("returnNewBoxTwoLevels")

    @Test
    fun `result variable reassigned by a clean call to the same factory`() = notReachable("returnNewBoxReassigned")

    @Test
    fun `clean instance from the factory that also built a tainted one`() = notReachable("returnNewBoxSeparateInstances")

    @Test
    fun `constructor stores its argument into a field`() = reachable("constructorStoresField")

    @Test
    fun `constructor stores the tainted argument into another field`() = notReachable("constructorStoresOtherField")

    @Test
    fun `fluent builder chain, field read on the built object`() = reachable("builderChainField")

    @Test
    fun `fluent builder chain, clean field read on the built object`() = notReachable("builderChainOtherField")

    @Test
    fun `callee writes the argument's field`() = reachable("calleeFillsArgField")

    @Test
    fun `callee overwrites a tainted argument field with a constant`() = notReachable("calleeOverwritesArgField")

    @Test
    fun `second fill call with a constant kills the first`() = notReachable("calleeOverwriteTwice")

    @Test
    fun `callee writes the argument's field through a local alias`() = reachable("calleeFillsThroughLocalAlias")

    @Test
    fun `getter returns the tainted field`() = reachable("getterReturnsField")

    @Test
    fun `getter returns an untainted field`() = notReachable("getterReturnsOtherField")

    @Test
    fun `depth-2 field chain written and read in different methods`() = reachable("nestedDepth2AcrossMethods")

    @Test
    fun `depth-3 field chain written and read in different methods`() = reachable("nestedDepth3AcrossMethods")

    @Test
    fun `depth-3 chain, sibling leaf read`() = notReachable("nestedDepth3OtherLeaf")

    @Test
    fun `field strongly overwritten with a constant`() = notReachable("fieldOverwriteKill")

    @Test
    fun `local reassigned with a constant`() = notReachable("localReassignKill")

    @Test
    fun `tainted field f, sink reads g`() = notReachable("unrelatedFieldWrite")

    @Test
    fun `tainted field of another object`() = notReachable("unrelatedObjectSameField")

    @Test
    fun `write through a local alias, read through the original`() = reachable("localAliasWrite")

    @Test
    fun `overwrite through a local alias kills the original's field`() = notReachable("localAliasOverwrite")

    @Test
    fun `write through an alias read back from a heap field`() = reachable("heapAliasWrite")

    @Test
    fun `setter then getter on the same object`() = reachable("thisFieldState")

    @Test
    fun `setter, reset to constant, getter`() = notReachable("thisFieldStateReset")

    @Test
    fun `static field written in one callee, read in another`() = reachable("staticFieldAcrossMethods")

    @Test
    fun `static field overwritten with a constant before the read`() = notReachable("staticFieldOverwritten")

    @Test
    fun `array element survives a write to another index`() = reachable("arrayWeakUpdate")

    @Test
    fun `element of a different array`() = notReachable("arrayDifferentArray")

    @Test
    fun `callee writes the array element`() = reachable("arrayFilledInCallee")

    @Test
    fun `list add and get via default pass-through rules`() = reachable("listAddGet")

    @Test
    fun `clean list next to a tainted one`() = notReachable("listOtherList")

    @Test
    fun `StringBuilder append chain via default pass-through rules`() = reachable("stringBuilderChain")

    @Test
    fun `string concatenation in a callee, then trim`() = reachable("stringConcatInCallee")

    @Test
    fun `recursive identity`() = reachable("recursionPassThrough")

    @Test
    fun `recursion that returns a constant`() = notReachable("recursionDropsValue")

    @Test
    fun `value shifted between locals over loop iterations`() = reachable("loopShiftsValue")

    @Test
    fun `value shifted between fields inside a loop`() = reachable("loopFieldShift")

    @Test
    fun `one of two implementations returns a source`() = reachable("virtualDispatchTaintingImpl")

    @Test
    fun `one of two implementations sinks its argument`() = reachable("virtualDispatchSinkingImpl")

    @Test
    fun `lambda returns a captured tainted local`() = reachable("lambdaCapturesTainted")

    @Test
    fun `lambda calls the source`() = reachable("lambdaReturnsSource")

    @Test
    fun `lambda ignores its tainted argument`() = notReachable("lambdaIgnoresArgument")

    @Test
    fun `identity lambda`() = reachable("lambdaPassesArgument")

    @Test
    fun `ternary merging a source and a constant`() = reachable("ternaryMerge")

    @Test
    fun `ternary of two constants`() = notReachable("ternaryBothSafe")

    @Test
    fun `source returned through two call levels`() = reachable("sourceTwoLevelsDeep")

    @Test
    fun `sink reached via parameter through two call levels`() = reachable("sinkTwoLevelsDeep")

    @Test
    fun `callee sinks a constant, not its parameter`() = notReachable("sinkInCalleeIgnoresParam")

    @Test
    fun `field of a parameter returned through an identity chain`() = reachable("returnParamFieldAfterChain")

    @Test
    fun `field overwritten only on one branch`() = reachable("conditionalOverwrite")

    @Test
    fun `callee overwrites the field only on one branch`() = reachable("conditionalOverwriteInCallee")

    @Test
    fun `callee moves f into g`() = reachable("calleeMovesFieldTarget")

    @Test
    fun `callee moves f into g and clears f`() = notReachable("calleeMovesFieldSource")

    @Test
    fun `callee copies a field from one argument to another`() = reachable("copyFieldBetweenObjects")

    @Test
    fun `callee copies the clean field over the tainted one`() = notReachable("copyFieldReversedDirection")

    @Test
    fun `field swap, read the field that received the taint`() = reachable("swapFields")

    @Test
    fun `field swap, read the field that lost the taint`() = notReachable("swapFieldsKillsOld")

    @Test
    fun `field re-wrapped into a fresh object by a callee`() = reachable("rewrapThroughNewObject")

    @Test
    fun `factory result stored in a heap field and read back`() = reachable("boxStoredInHolderReturned")

    private fun reachableAtSinks(entryPoint: String, vararg expectedSinkIndices: Int) {
        val method = cp.findClassOrNull(TEST_CLS)!!.declaredMethods.single { it.name == entryPoint }
        val sinkCalls = method.instList.filter { inst ->
            inst.callExpr?.method?.name == "sink"
        }
        val reported = runAnalysis(config, TEST_CLS, entryPoint).map { vt ->
            assertEquals(RULE_ID, vt.vulnerability.rule.id, entryPoint)
            sinkCalls.indexOf(vt.vulnerability.statement)
        }.toSet()
        assertEquals(expectedSinkIndices.toSet(), reported, "$entryPoint: reported sink indices")
    }

    @Test
    fun `static field written in the caller and read in a callee`() = reachable("staticWrittenInCallerReadInCallee")

    @Test
    fun `static field read before a callee taints it`() = notReachable("staticReadBeforeWrite")

    @Test
    fun `field read before it is tainted`() = notReachable("fieldReadBeforeWrite")

    @Test
    fun `callee sinks a field of its argument`() = reachable("sinkOnArgumentFieldInCallee")

    @Test
    fun `callee sinks a clean field of its argument`() = notReachable("sinkOnOtherArgumentFieldInCallee")

    @Test
    fun `callee writes an unrelated field of the argument`() = reachable("calleeTouchesOtherField")

    @Test
    fun `callee replaces the held box with a clean one`() = notReachable("calleeReplacesHeldBox")

    @Test
    fun `reference read before the callee replaces the held box`() = reachable("oldReferenceSurvivesReplace")

    @Test
    fun `field chain built by nested factories`() = reachable("nestedFactories")

    @Test
    fun `field chain built by nested factories, sibling leaf read`() = notReachable("nestedFactoriesOtherLeaf")

    @Test
    fun `lambda sinks a captured tainted local`() = reachable("lambdaSinksCaptured")

    @Test
    fun `lambda sinks a captured clean local`() = notReachable("lambdaSinksCapturedClean")

    @Test
    fun `sinking lambda passed to a higher-order helper`() = reachable("higherOrderSinkLambda")

    @Test
    fun `receiver of a known clean implementation`() = notReachable("knownReceiverCleanImpl")

    @Test
    fun `callee swaps a field between two arguments, receiver read`() = reachable("swapArgsReceiver")

    @Test
    fun `callee swaps a field between two arguments, donor read`() = notReachable("swapArgsDonor")

    @Test
    fun `same object passed as both arguments, fill after clear`() = reachable("sameObjectPassedTwice")

    @Test
    fun `call result assigned to its own argument variable`() = reachable("resultAssignedToArgumentVariable")

    @Test
    fun `fresh call result replaces its argument variable`() = notReachable("resultReplacesArgumentVariable")

    @Test
    fun `identity call result assigned to its own argument variable`() = reachable("stringResultAssignedToArgument")

    @Test
    fun `callee taints the argument then reassigns the parameter`() = reachable("calleeReassignsParameter")

    @Test
    fun `this field tainted by one callee and sunk by another`() = reachable("entryThisFieldInitUse")

    @Test
    fun `this field reset between the tainting and sinking callees`() = notReachable("entryThisFieldInitResetUse")

    @Test
    fun `library pass-through mutates an argument inside a callee`() = reachable("libraryMutationInCallee")

    @Test
    fun `library pass-through on a local alias`() = reachable("libraryMutationThroughAlias")

    @Test
    fun `field of a box stored in an array element`() = reachable("arrayOfBoxes")

    @Test
    fun `copy through a constructor, clean field read`() = notReachable("copyConstructorOtherField")

    @Test
    fun `copy through a constructor, tainted field read`() = reachable("copyConstructorField")

    @Test
    fun `one branch builds a tainted box`() = reachable("conditionalFactoryResult")

    @Test
    fun `only the sink before the kill is reported`() = reachableAtSinks("killBetweenTwoSinks", 0)

    @Test
    fun `only the sink after the taint is reported`() = reachableAtSinks("taintBetweenTwoSinks", 1)

    @Test
    fun `only the sink of the tainted box is reported`() = reachableAtSinks("twoSinksDifferentBoxes", 1)

    @Test
    fun `callee sinks its parameter and never returns`() = reachable("calleeWithoutNormalExit")

    @Test
    fun `callee sinks its parameter and always throws`() = reachable("calleeSinksThenThrows")

    @Test
    fun `sink in a loop left only by throwing`() = reachable("sinkInLoopExitOnlyByThrow")

    @Test
    fun `sink in a finally block`() = reachable("finallySink")

    @Test
    fun `callee sinks a static field tainted by the caller`() = reachable("sinkOnStaticInCallee")

    @Test
    fun `getter returns a held box whose field is tainted`() = reachable("getterOfHeldBox")

    @Test
    fun `callee links a tainted box into a holder`() = reachable("setterCreatesHeapLink")

    @Test
    fun `callee replaces an intermediate object of a field chain`() = notReachable("calleeReplacesIntermediateObject")

    @Test
    fun `intermediate reference read before the callee replaces it`() = reachable("intermediateReferenceSurvives")

    @Test
    fun `generic field read with a checkcast`() = reachable("genericFieldWithCast")

    @Test
    fun `Object-typed local cast back to the box`() = reachable("objectTypedLocalCast")

    @Test
    fun `field of a box read back from a list`() = reachable("listOfBoxesField")

    @Test
    fun `callee returns either argument`() = reachable("chooseEitherArgument")

    @Test
    fun `mutual recursion passes the value through`() = reachable("mutualRecursion")

    @Test
    fun `depth-5 field chain written and read in different methods`() = reachable("depth5AcrossMethods")

    @Test
    fun `field of the same name in another class`() = notReachable("sameFieldNameOtherClass")

    @Test
    fun `inherited field read through the supertype`() = reachable("subclassFieldViaSuperType")

    @Test
    fun `shadowing subclass field is not the superclass field`() = notReachable("shadowedFieldNotConfused")

    @Test
    fun `super constructor stores the argument`() = reachable("superConstructorStoresField")

    @Test
    fun `callee mutates the argument whose variable receives the result`() = reachable("argumentMutatedButVariableReplaced")

    @Test
    fun `fresh result read after the callee mutated the argument`() = notReachable("argumentMutatedResultRead")

    @Test
    fun `array copied with System arraycopy`() = reachable("arrayCopy")

    @Test
    fun `entry parameter without a source`() = notReachable("entryParameterOnly")

    @Test
    fun `builder read before it is reset`() = reachable("builderReadThenReset")

    @Test
    fun `String format with a varargs array`() = reachable("stringFormatVarargs")

    @Test
    fun `for-each loop over a tainted list`() = reachable("iteratorLoopSink")

    @Test
    fun `inner class sinks a field of its outer instance`() = reachable("innerClassReadsOuterField")

    @Test
    fun `Objects requireNonNull keeps the fields`() = reachable("requireNonNullKeepsFields")

    @Test
    fun `unmodelled library call keeps the argument's taint`() = reachable("unmodelledLibraryCallKeepsArgument")

    @Test
    fun `sink through a method reference`() = reachable("methodReferenceSink")

    @Test
    fun `supplier lambda created in a callee`() = reachable("lambdaCreatedInCallee")

    @Test
    fun `supplier lambda stored in a field`() = reachable("lambdaStoredInField")

    @Test
    fun `higher-order helper, tainted value given to the constant lambda`() = notReachable("helperWithTwoLambdas")

    @Test
    fun `higher-order helper, tainted value given to the identity lambda`() = reachable("helperWithTwoLambdasTainting")

    @Test
    fun `catch block sinks a local tainted in the try block`() = reachable("catchUsesTryLocal")

    @Test
    fun `callee sinks its parameter and rarely returns`() = reachable("calleeWithRareExit")
}
