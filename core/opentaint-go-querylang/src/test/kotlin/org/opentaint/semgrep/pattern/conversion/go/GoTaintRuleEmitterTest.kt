package org.opentaint.semgrep.pattern.conversion.go

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedFunctionNameMatcher
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedSimpleNameMatcher
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintPassAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedItem
import org.opentaint.dataflow.go.rules.TaintRules
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class GoTaintRuleEmitterTest {

    /** A function matcher with empty package, the given class (Go package selector) and name. */
    private fun fn(cls: String, name: String): SerializedFunctionNameMatcher =
        SerializedFunctionNameMatcher.Complex(
            `package` = SerializedSimpleNameMatcher.Simple(""),
            `class` = SerializedSimpleNameMatcher.Simple(cls),
            name = SerializedSimpleNameMatcher.Simple(name),
        )

    private fun baseOnly(pos: PositionBase) = PositionBaseWithModifiers.BaseOnly(pos)

    private fun rule(vararg items: SerializedItem): TaintRuleFromSemgrep =
        TaintRuleFromSemgrep("r", listOf(TaintRuleFromSemgrep.TaintRuleGroup(items.toList())))

    @Test
    fun `source taints the result of a named function`() {
        val rule = rule(
            SerializedRule.Source(
                function = fn("util", "Source"),
                taint = listOf(SerializedTaintAssignAction("taint", pos = baseOnly(PositionBase.Result))),
            ),
        )

        val emitter = GoTaintRuleEmitter()
        val cfg = emitter.emit("r", rule)

        assertEquals(listOf(TaintRules.Source("util.Source", "taint", PositionBase.Result)), cfg.sources)
        assertTrue(emitter.dropped.isEmpty())
    }

    @Test
    fun `source with no taint action defaults to Result`() {
        val rule = rule(
            SerializedRule.Source(function = fn("util", "Source"), taint = emptyList()),
        )

        val cfg = GoTaintRuleEmitter().emit("r", rule)

        assertEquals(PositionBase.Result, cfg.sources.single().pos)
    }

    @Test
    fun `sink position is read from the first ContainsMark in its condition`() {
        val rule = rule(
            SerializedRule.Sink(
                function = fn("util", "Sink"),
                condition = SerializedCondition.ContainsMark("taint", baseOnly(PositionBase.Argument(0))),
            ),
        )

        val emitter = GoTaintRuleEmitter()
        val cfg = emitter.emit("rule-id", rule)

        val sink = cfg.sinks.single()
        assertEquals("util.Sink", sink.function)
        assertEquals(PositionBase.Argument(0), sink.pos)
        assertEquals("rule-id", sink.id)
        assertTrue(emitter.dropped.isEmpty())
    }

    @Test
    fun `sink finds ContainsMark nested under And`() {
        val rule = rule(
            SerializedRule.Sink(
                function = fn("db", "Exec"),
                id = "explicit-id",
                condition = SerializedCondition.and(
                    listOf(
                        SerializedCondition.NumberOfArgs(2),
                        SerializedCondition.ContainsMark("taint", baseOnly(PositionBase.Argument(1))),
                    ),
                ),
            ),
        )

        val sink = GoTaintRuleEmitter().emit("r", rule).sinks.single()
        assertEquals("db.Exec", sink.function)
        assertEquals(PositionBase.Argument(1), sink.pos)
        assertEquals("explicit-id", sink.id)
    }

    @Test
    fun `sink with no ContainsMark falls back to argument 0`() {
        val rule = rule(
            SerializedRule.Sink(function = fn("util", "Sink"), condition = null),
        )

        val sink = GoTaintRuleEmitter().emit("r", rule).sinks.single()
        assertEquals(PositionBase.Argument(0), sink.pos)
    }

    @Test
    fun `pass maps the first copy action`() {
        val rule = rule(
            SerializedRule.PassThrough(
                function = fn("util", "Wrap"),
                copy = listOf(
                    SerializedTaintPassAction(
                        from = baseOnly(PositionBase.Argument(0)),
                        to = baseOnly(PositionBase.Result),
                    ),
                ),
            ),
        )

        val emitter = GoTaintRuleEmitter()
        val pass = emitter.emit("r", rule).propagators.single()

        assertEquals("util.Wrap", pass.function)
        assertEquals(baseOnly(PositionBase.Argument(0)), pass.from)
        assertEquals(baseOnly(PositionBase.Result), pass.to)
        assertTrue(emitter.dropped.isEmpty())
    }

    @Test
    fun `unnameable function (pattern name) is dropped and counted`() {
        val rule = rule(
            SerializedRule.Source(
                function = SerializedFunctionNameMatcher.Complex(
                    `package` = SerializedSimpleNameMatcher.Simple(""),
                    `class` = SerializedSimpleNameMatcher.Simple("util"),
                    name = SerializedSimpleNameMatcher.Pattern(".*"),
                ),
                taint = listOf(SerializedTaintAssignAction("taint", pos = baseOnly(PositionBase.Result))),
            ),
        )

        val emitter = GoTaintRuleEmitter()
        val cfg = emitter.emit("r", rule)

        assertTrue(cfg.sources.isEmpty())
        assertEquals(1, emitter.dropped["source_unnameable"])
    }

    @Test
    fun `pass with no copy action is dropped and counted`() {
        val rule = rule(
            SerializedRule.PassThrough(function = fn("util", "Wrap"), copy = emptyList()),
        )

        val emitter = GoTaintRuleEmitter()
        val cfg = emitter.emit("r", rule)

        assertTrue(cfg.propagators.isEmpty())
        assertEquals(1, emitter.dropped["pass_no_copy"])
    }
}
