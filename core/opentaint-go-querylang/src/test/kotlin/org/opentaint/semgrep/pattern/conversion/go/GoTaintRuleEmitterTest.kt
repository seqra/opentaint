package org.opentaint.semgrep.pattern.conversion.go

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.go.rules.serialized.GoFunctionMatcher
import org.opentaint.dataflow.go.rules.serialized.GoSerializedAssignAction
import org.opentaint.dataflow.go.rules.serialized.GoSerializedCleanAction
import org.opentaint.dataflow.go.rules.serialized.GoSerializedCondition
import org.opentaint.dataflow.go.rules.serialized.GoSerializedItem
import org.opentaint.dataflow.go.rules.serialized.GoSerializedPassAction
import org.opentaint.dataflow.go.rules.serialized.GoSerializedRule
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class GoTaintRuleEmitterTest {

    private fun baseOnly(pos: PositionBase) = PositionBaseWithModifiers.BaseOnly(pos)

    private fun rule(vararg items: GoSerializedItem): TaintRuleFromSemgrep<GoSerializedItem> =
        TaintRuleFromSemgrep("r", listOf(TaintRuleFromSemgrep.TaintRuleGroup(items.toList())))

    @Test
    fun `source taints the result of a named function`() {
        val rule = rule(
            GoSerializedRule.Source(
                function = GoFunctionMatcher.Simple("util.Source"),
                condition = null,
                taint = listOf(GoSerializedAssignAction("taint", baseOnly(PositionBase.Result))),
            ),
        )

        val cfg = GoTaintRuleEmitter().emit("r", rule)

        val src = cfg.sourceForFunction("util.Source").single()
        assertEquals("util.Source", src.function)
        assertEquals("taint", src.actionsAfter.single().mark)
        assertEquals(baseOnly(PositionBase.Result), src.actionsAfter.single().pos)
    }

    @Test
    fun `source with no taint action emits no actions`() {
        val rule = rule(
            GoSerializedRule.Source(
                function = GoFunctionMatcher.Simple("util.Source"),
                condition = null,
                taint = emptyList(),
            ),
        )

        val cfg = GoTaintRuleEmitter().emit("r", rule)
        assertTrue(cfg.sourceForFunction("util.Source").single().actionsAfter.isEmpty())
    }

    @Test
    fun `sink with explicit id is preserved`() {
        val rule = rule(
            GoSerializedRule.Sink(
                function = GoFunctionMatcher.Simple("util.Sink"),
                condition = GoSerializedCondition.ContainsMark("taint", baseOnly(PositionBase.Argument(0))),
                id = "explicit-id",
            ),
        )

        val cfg = GoTaintRuleEmitter().emit("r", rule)
        val sink = cfg.sinkForFunction("util.Sink").single()
        assertEquals("util.Sink", sink.function)
        assertEquals("explicit-id", sink.id)
    }

    @Test
    fun `pass-through copy action is resolved`() {
        val rule = rule(
            GoSerializedRule.PassThrough(
                function = GoFunctionMatcher.Simple("util.Wrap"),
                copy = listOf(
                    GoSerializedPassAction(
                        from = baseOnly(PositionBase.Argument(0)),
                        to = baseOnly(PositionBase.Result),
                    ),
                ),
            ),
        )

        val cfg = GoTaintRuleEmitter().emit("r", rule)
        val pass = cfg.passThroughForFunction("util.Wrap").single()
        assertEquals("util.Wrap", pass.function)
        assertEquals(1, pass.actionsAfter.size)
    }

    @Test
    fun `pattern-matcher rules resolve on callee-name lookup`() {
        val rule = rule(
            GoSerializedRule.Source(
                function = GoFunctionMatcher.Pattern("util\\..*"),
                condition = null,
                taint = listOf(GoSerializedAssignAction("taint", baseOnly(PositionBase.Result))),
            ),
        )

        // The pattern matcher survives — querying a concrete callee name that matches the
        // pattern materializes the rule on demand.
        val cfg = GoTaintRuleEmitter().emit("r", rule)
        assertTrue(cfg.sourceForFunction("util.Foo").isNotEmpty())
        assertTrue(cfg.sourceForFunction("util.Bar").isNotEmpty())
        // A name that does NOT match the pattern returns no rules.
        assertTrue(cfg.sourceForFunction("other.Foo").isEmpty())
    }

    @Test
    fun `cleaner rule is resolved`() {
        val rule = rule(
            GoSerializedRule.Cleaner(
                function = GoFunctionMatcher.Simple("util.Clean"),
                cleans = listOf(GoSerializedCleanAction("taint", baseOnly(PositionBase.Argument(0)))),
            ),
        )

        val cfg = GoTaintRuleEmitter().emit("r", rule)
        assertEquals(1, cfg.cleanerForFunction("util.Clean").size)
        assertEquals("util.Clean", cfg.cleanerForFunction("util.Clean").single().function)
    }
}
