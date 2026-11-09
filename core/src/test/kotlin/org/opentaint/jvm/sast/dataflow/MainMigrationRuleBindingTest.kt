package org.opentaint.jvm.sast.dataflow

import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.jvm.ActionPosition
import org.opentaint.dataflow.configuration.jvm.Argument
import org.opentaint.dataflow.configuration.jvm.ContainsMark
import org.opentaint.dataflow.configuration.jvm.PositionAccessor
import org.opentaint.dataflow.configuration.jvm.PositionWithAccess
import org.opentaint.dataflow.configuration.jvm.TaintMark
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintCleanAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.taint.ContainsMarkOnAnyField
import org.opentaint.jvm.sast.dataflow.rules.TaintConfiguration
import kotlin.test.Test
import org.junit.jupiter.api.Assertions.assertEquals
import kotlin.test.assertTrue

/** Native controls for the public reach encoding and the existing per-action cleaner split. */
class MainMigrationRuleBindingTest : AnalysisTest() {
    override val sourceFileExtension = "java"
    private val owner = "test.samples.DeepCleanSummarySample"
    private val root = PositionBaseWithModifiers.BaseOnly(PositionBase.Argument(0))
    private val below = PositionBaseWithModifiers.WithModifiers(PositionBase.Argument(0), listOf(PositionModifier.AnyField))
    private val field = PositionModifier.Field("test.samples.DeepCleanSummarySample\$Box", "f", "java.lang.String")
    private val mark = TaintMark("M")

    private fun cleaners(condition: SerializedCondition?, position: PositionBaseWithModifiers = below) =
        TaintConfiguration(cp).apply {
            loadConfig(SerializedTaintConfig(cleaner = listOf(SerializedRule.Cleaner(
                functionMatcher(owner, "clean"), condition = condition,
                cleans = listOf(SerializedTaintCleanAction("M", position)), serializedId = "clean-label"))))
        }.cleanerForMethod(findMethod(owner, "clean"), allRelevant = false)

    @Test fun `below cleaner assumes below containment and does not assume a root mark`() {
        val rows = cleaners(SerializedCondition.ContainsMark("M", root))
        assertEquals(CommonCondition.Atom(ContainsMark(Argument(0), mark)), rows.single().condition)
        assertEquals(ActionPosition.AnyAccessorAfter(Argument(0)), rows.single().actionsAfter.single().let {
            (it as org.opentaint.dataflow.configuration.jvm.RemoveMark).position
        })
        assertEquals("clean-label", rows.single().serializedId)
    }

    @Test fun `canonical any-field condition is assumed without a root mark`() {
        assertEquals(CommonCondition.True,
            cleaners(SerializedCondition.ContainsMark("M", below)).single().condition)
        assertTrue(cleaners(SerializedCondition.Not(SerializedCondition.ContainsMark("M", below))).isEmpty())
    }

    @Test fun `below assumption keeps unrelated conjunction leaves`() {
        val unrelated = SerializedCondition.ContainsMark("U", root)
        val condition = SerializedCondition.And(listOf(SerializedCondition.ContainsMark("M", below), unrelated))
        assertEquals(CommonCondition.Atom(ContainsMark(Argument(0), TaintMark("U"))), cleaners(condition).single().condition)
    }

    @Test fun `first any-field marker fixes the action prefix and ignores later modifiers`() {
        val position = PositionBaseWithModifiers.WithModifiers(PositionBase.Argument(0),
            listOf(field, PositionModifier.AnyField, PositionModifier.ArrayElement, field))
        val expected = PositionWithAccess(Argument(0), PositionAccessor.FieldAccessor(
            field.className, field.fieldName, field.fieldType))
        val row = cleaners(null, position).single()
        assertEquals(ActionPosition.AnyAccessorAfter(expected),
            (row.actionsAfter.single() as org.opentaint.dataflow.configuration.jvm.RemoveMark).position)
    }

    @Test fun `first any-field marker fixes the condition prefix too`() {
        val position = PositionBaseWithModifiers.WithModifiers(PositionBase.Argument(0),
            listOf(field, PositionModifier.AnyField, PositionModifier.ArrayElement))
        val row = cleaners(SerializedCondition.ContainsMark("M", position), root).single()
        val expected = PositionWithAccess(Argument(0), PositionAccessor.FieldAccessor(
            field.className, field.fieldName, field.fieldType))
        assertEquals(CommonCondition.Atom(ContainsMarkOnAnyField(expected, mark)), row.condition)
    }

    @Test fun `source binding distinguishes exact reach from explicit descendant reach`() {
        val config = TaintConfiguration(cp).apply {
            loadConfig(SerializedTaintConfig(source = listOf(SerializedRule.Source(
                functionMatcher(owner, "clean"), taint = listOf(
                    SerializedTaintAssignAction("M", pos = root),
                    SerializedTaintAssignAction("M", pos = below)), serializedId = "source-label"))))
        }
        val row = config.sourceForMethod(findMethod(owner, "clean"), allRelevant = false).single()
        assertEquals(listOf(ActionPosition.Exact(Argument(0)), ActionPosition.AnyAccessorAfter(Argument(0))),
            row.actionsAfter.map { it.position })
        assertEquals("source-label", row.serializedId)
    }
}
