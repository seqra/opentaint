package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.taint.PrimitiveTaintExt

/**
 * The propagation shapes DataFlowBench reports as false negatives for the JVM engine, restated as
 * source/sink dataflow tests.
 *
 * Each missed shape is paired with a control that isolates its cause, so a fix can be attributed
 * rather than guessed. The benchmark drives one Semgrep rule with `primitive-tracking: true`; the
 * equivalent here is the [PrimitiveTaintExt.PRIMITIVE_TRACKING_ENABLED_MODE] mark suffix, used for
 * every mark so that the numeric and reference arms of a pair differ only in the value type.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class DataFlowBenchFalseNegativeTest : AnalysisTest() {

    companion object {
        const val SAMPLE_PACKAGE = "test.samples"
        const val TAINT_MARK = "tainted" + PrimitiveTaintExt.PRIMITIVE_TRACKING_ENABLED_MODE
    }

    override val useDefaultConfig: Boolean = true

    /**
     * Enabled so these tests mirror the production analyzer, which runs the built-in library model
     * unless `--disable-default-get-model` is passed. The fixtures themselves are excluded, exactly
     * as production excludes project classes.
     */
    /**
     * A config carrying both the numeric and the reference endpoint pair, so the two arms of a
     * shape are analyzed under one rule set.
     */
    protected fun benchConfig(
        testCls: String,
        ruleId: String,
        intEndpoints: Boolean = true,
    ): SerializedTaintConfig {
        val sources = mutableListOf<SerializedRule.Source>(sourceRule(testCls, "source", TAINT_MARK))
        val sinks = mutableListOf(
            sinkRule(testCls, "sink", ruleId, listOf<Pair<PositionBase, String>>(Argument(0) to TAINT_MARK))
        )

        if (intEndpoints) {
            sources += sourceRule(testCls, "intSource", TAINT_MARK)
            sinks += sinkRule(
                testCls, "intSink", ruleId, listOf<Pair<PositionBase, String>>(Argument(0) to TAINT_MARK)
            )
        }

        return SerializedTaintConfig(source = sources, sink = sinks)
    }
}

/**
 * Java arm. All four templates DataFlowBench misses on the Java kernel are here, each with the
 * control that pins its cause.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class JavaDataFlowBenchFalseNegativeTest : DataFlowBenchFalseNegativeTest() {

    override val sourceFileExtension: String = "java"

    // region map iteration -- the taint crosses a map entry read.
    // The numeric arm is the benchmark miss; the reference arm is the control that separates the
    // value kind from the entry-iteration modelling.

    // Was a false negative until java-lang.yaml modelled the boxing pair. The taint used to die at
    // the compiler-inserted `%3 = Integer.valueOf(%2)`: an unresolved JDK callee with no
    // pass-through, so `put` already saw a clean argument. Box and unbox are independent barriers --
    // modelling only `valueOf` leaves this failing at `%16.intValue()`.
    @Test
    fun `map iteration - Integer-valued entry reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.DataFlowBenchMapIterationSample"

        assertReachable(
            config = benchConfig(testCls, MAP_RULE_ID),
            testCls = testCls,
            entryPointName = "mapIterationIntFlow",
            ruleId = MAP_RULE_ID,
            testName = "map entry iteration, Integer value"
        )
    }

    @Test
    fun `map iteration - String-valued entry reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.DataFlowBenchMapIterationSample"

        assertReachable(
            config = benchConfig(testCls, MAP_RULE_ID),
            testCls = testCls,
            entryPointName = "mapIterationStringFlow",
            ruleId = MAP_RULE_ID,
            testName = "map entry iteration, String value"
        )
    }
    // endregion

    // region callback registration -- the callee is recovered from a collection before it is called.
    // Both arms are benchmark misses. The two controls below show that neither the lambda nor the
    // list traversal is missing on its own, so the gap is the combination.

    // Was a false negative until prescan kept its pass-through rules. Lambda callee resolution runs
    // only in prescan (JIRMethodCallResolver.kt:120, :147), and prescan used to wipe every config
    // rule including pass-through -- which is the only model for Collection#add / Iterator#next. The
    // lambda's TypeInfoAccessor fact could not cross the list, so the body was analyzed in neither
    // phase. Never a value-kind miss: the String arm below fails and recovers identically.
    @Test
    fun `callback registration - int-typed hook read from a list reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.DataFlowBenchCallbackSample"

        assertReachable(
            config = benchConfig(testCls, CALLBACK_RULE_ID),
            testCls = testCls,
            entryPointName = "callbackIntFlow",
            ruleId = CALLBACK_RULE_ID,
            testName = "callback registration, int hook"
        )
    }

    // The reference-typed twin of the arm above -- it is what rules the value kind out as a cause.
    @Test
    fun `callback registration - String-typed hook read from a list reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.DataFlowBenchCallbackSample"

        assertReachable(
            config = benchConfig(testCls, CALLBACK_RULE_ID),
            testCls = testCls,
            entryPointName = "callbackStringFlow",
            ruleId = CALLBACK_RULE_ID,
            testName = "callback registration, String hook"
        )
    }

    @Test
    fun `callback registration control - a lambda invoked directly reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.DataFlowBenchCallbackSample"

        assertReachable(
            config = benchConfig(testCls, CALLBACK_RULE_ID),
            testCls = testCls,
            entryPointName = "directLambdaFlow",
            ruleId = CALLBACK_RULE_ID,
            testName = "callback control, direct lambda"
        )
    }

    @Test
    fun `callback registration control - plain list iteration reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.DataFlowBenchCallbackSample"

        assertReachable(
            config = benchConfig(testCls, CALLBACK_RULE_ID),
            testCls = testCls,
            entryPointName = "listIterationFlow",
            ruleId = CALLBACK_RULE_ID,
            testName = "callback control, plain list iteration"
        )
    }
    // endregion

    // region exception catch -- the taint rides a field of a thrown exception across throw/catch.
    // Both arms are benchmark misses; the control writes and reads the same field without the
    // throw, so it separates the field from the exceptional edge.

    @Test
    // todo: the taint does not cross the throw/catch edge. Not a value-kind miss -- the String arm
    //  fails identically, and the control writes and reads the same field without the throw and
    //  does reach the sink.
    @Disabled
    fun `exception catch - int payload survives throw and catch`() {
        val testCls = "$SAMPLE_PACKAGE.DataFlowBenchExceptionCatchSample"

        assertReachable(
            config = benchConfig(testCls, EXCEPTION_RULE_ID),
            testCls = testCls,
            entryPointName = "exceptionCatchIntFlow",
            ruleId = EXCEPTION_RULE_ID,
            testName = "exception catch, int payload"
        )
    }

    @Test
    // todo: same missing throw/catch edge as the int arm above, reference-typed.
    @Disabled
    fun `exception catch - String payload survives throw and catch`() {
        val testCls = "$SAMPLE_PACKAGE.DataFlowBenchExceptionCatchSample"

        assertReachable(
            config = benchConfig(testCls, EXCEPTION_RULE_ID),
            testCls = testCls,
            entryPointName = "exceptionCatchStringFlow",
            ruleId = EXCEPTION_RULE_ID,
            testName = "exception catch, String payload"
        )
    }

    @Test
    fun `exception catch control - the carrier field alone reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.DataFlowBenchExceptionCatchSample"

        assertReachable(
            config = benchConfig(testCls, EXCEPTION_RULE_ID),
            testCls = testCls,
            entryPointName = "carrierFieldFlow",
            ruleId = EXCEPTION_RULE_ID,
            testName = "exception catch control, carrier field only"
        )
    }
    // endregion

    // region reflective invocation -- the callee is named by a run-time string.

    @Test
    // todo: Method#invoke on a callee named by a run-time string is not resolved to its body. The
    //  control calls the very same method directly and reaches the sink.
    @Disabled
    fun `reflective invocation - a string-resolved callee reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.DataFlowBenchReflectiveInvocationSample"

        assertReachable(
            config = benchConfig(testCls, REFLECTION_RULE_ID, intEndpoints = false),
            testCls = testCls,
            entryPointName = "reflectiveInvocationFlow",
            ruleId = REFLECTION_RULE_ID,
            testName = "reflective invocation"
        )
    }

    @Test
    fun `reflective invocation control - the same callee invoked directly reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.DataFlowBenchReflectiveInvocationSample"

        assertReachable(
            config = benchConfig(testCls, REFLECTION_RULE_ID, intEndpoints = false),
            testCls = testCls,
            entryPointName = "directInvocationFlow",
            ruleId = REFLECTION_RULE_ID,
            testName = "reflective invocation control, direct call"
        )
    }
    // endregion

    private companion object {
        const val MAP_RULE_ID = "dfb-map-iteration-rule"
        const val CALLBACK_RULE_ID = "dfb-callback-registration-rule"
        const val EXCEPTION_RULE_ID = "dfb-exception-catch-rule"
        const val REFLECTION_RULE_ID = "dfb-reflective-invocation-rule"
    }
}

/**
 * Kotlin arm. The Kotlin kernel misses only these two templates; the other two Java misses are
 * reported correctly there because those fixtures are reference-typed.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class KotlinDataFlowBenchFalseNegativeTest : DataFlowBenchFalseNegativeTest() {

    override val sourceFileExtension: String = "kt"

    @Test
    // todo: the Kotlin mirror of the Java throw/catch miss.
    @Disabled
    fun `exception catch - Int payload survives throw and catch`() {
        val testCls = "$SAMPLE_PACKAGE.KotlinDataFlowBenchExceptionCatchSample"

        assertReachable(
            config = benchConfig(testCls, EXCEPTION_RULE_ID),
            testCls = testCls,
            entryPointName = "exceptionCatchIntFlow",
            ruleId = EXCEPTION_RULE_ID,
            testName = "kotlin exception catch, Int payload"
        )
    }

    @Test
    // todo: same missing throw/catch edge, reference-typed.
    @Disabled
    fun `exception catch - String payload survives throw and catch`() {
        val testCls = "$SAMPLE_PACKAGE.KotlinDataFlowBenchExceptionCatchSample"

        assertReachable(
            config = benchConfig(testCls, EXCEPTION_RULE_ID),
            testCls = testCls,
            entryPointName = "exceptionCatchStringFlow",
            ruleId = EXCEPTION_RULE_ID,
            testName = "kotlin exception catch, String payload"
        )
    }

    @Test
    fun `exception catch control - the carrier field alone reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.KotlinDataFlowBenchExceptionCatchSample"

        assertReachable(
            config = benchConfig(testCls, EXCEPTION_RULE_ID),
            testCls = testCls,
            entryPointName = "carrierFieldFlow",
            ruleId = EXCEPTION_RULE_ID,
            testName = "kotlin exception catch control, carrier field only"
        )
    }

    @Test
    // todo: the Kotlin mirror of the Java reflection miss. Reference-typed in both languages, so
    //  the value kind is not involved here at all.
    @Disabled
    fun `reflective invocation - a string-resolved callee reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.KotlinDataFlowBenchReflectiveInvocationSample"

        assertReachable(
            config = benchConfig(testCls, REFLECTION_RULE_ID, intEndpoints = false),
            testCls = testCls,
            entryPointName = "reflectiveInvocationFlow",
            ruleId = REFLECTION_RULE_ID,
            testName = "kotlin reflective invocation"
        )
    }

    @Test
    fun `reflective invocation control - the same callee invoked directly reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.KotlinDataFlowBenchReflectiveInvocationSample"

        assertReachable(
            config = benchConfig(testCls, REFLECTION_RULE_ID, intEndpoints = false),
            testCls = testCls,
            entryPointName = "directInvocationFlow",
            ruleId = REFLECTION_RULE_ID,
            testName = "kotlin reflective invocation control, direct call"
        )
    }

    private companion object {
        const val EXCEPTION_RULE_ID = "dfb-kt-exception-catch-rule"
        const val REFLECTION_RULE_ID = "dfb-kt-reflective-invocation-rule"
    }
}
