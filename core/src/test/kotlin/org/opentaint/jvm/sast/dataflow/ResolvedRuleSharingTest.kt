package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedFunctionNameMatcher
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedSimpleNameMatcher
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.jvm.sast.ast.BasicTestUtils
import org.opentaint.jvm.sast.dataflow.rules.TaintConfiguration
import kotlin.test.assertEquals
import kotlin.test.assertSame
import kotlin.test.assertTrue

class ResolvedRuleSharingTest : BasicTestUtils() {
    override val sourceFileExtension: String get() = "java"

    private fun anyName() = SerializedSimpleNameMatcher.Pattern(".*")

    private fun anyFunction() =
        SerializedFunctionNameMatcher.Complex(anyName(), anyName(), anyName())

    private fun exitSinkRule() = SerializedRule.MethodExitSink(
        function = anyFunction(),
        condition = SerializedCondition.ContainsMark(
            tainted = "shared-test-mark",
            pos = PositionBaseWithModifiers.BaseOnly(PositionBase.Result),
        ),
        id = "shared-test-sink",
        meta = SinkMetaData(cwe = listOf(79), note = "shared meta"),
    )

    private fun stringMethods(): Pair<JIRMethod, JIRMethod> {
        val stringClass = findClass("java.lang.String")
        val trim = stringClass.declaredMethods.single { it.name == "trim" && it.parameters.isEmpty() }
        val toLower = stringClass.declaredMethods.single { it.name == "toLowerCase" && it.parameters.isEmpty() }
        return trim to toLower
    }

    @Test
    fun `resolved rules for distinct methods share condition, meta and actions`() {
        val configuration = TaintConfiguration(cp)
        configuration.loadConfig(SerializedTaintConfig(methodExitSink = listOf(exitSinkRule())))

        val (first, second) = stringMethods()

        val firstRules = configuration.methodExitSinkForMethod(first, allRelevant = false)
        val secondRules = configuration.methodExitSinkForMethod(second, allRelevant = false)

        assertEquals(1, firstRules.size)
        assertEquals(1, secondRules.size)

        val a = firstRules.single()
        val b = secondRules.single()

        assertTrue(a.method !== b.method)
        assertSame(a.condition, b.condition)
        assertSame(a.meta, b.meta)
        assertEquals(a.id, b.id)
    }

    @Test
    fun `sharing preserves resolved rule values`() {
        val rule = exitSinkRule()

        val shared = TaintConfiguration(cp)
        shared.loadConfig(SerializedTaintConfig(methodExitSink = listOf(rule)))

        val (first, second) = stringMethods()

        val sharedFirst = shared.methodExitSinkForMethod(first, allRelevant = false).single()

        val isolated = TaintConfiguration(cp)
        isolated.loadConfig(SerializedTaintConfig(methodExitSink = listOf(rule)))
        val isolatedFirst = isolated.methodExitSinkForMethod(first, allRelevant = false).single()

        assertEquals(isolatedFirst, sharedFirst)
        assertEquals(isolatedFirst.condition, sharedFirst.condition)
        assertEquals(isolatedFirst.meta, sharedFirst.meta)

        val sharedSecond = shared.methodExitSinkForMethod(second, allRelevant = false).single()
        assertEquals(second, sharedSecond.method)
        assertEquals(isolatedFirst.condition, sharedSecond.condition)
    }
}
