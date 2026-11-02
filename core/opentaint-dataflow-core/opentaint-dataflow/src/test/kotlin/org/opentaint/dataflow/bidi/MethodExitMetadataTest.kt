package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.finishMethodData
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import kotlin.test.*

class MethodExitMetadataTest {
    private fun rule(id: String) = object : CommonTaintConfigurationSink {
        override val id = id
        override val meta = object : CommonTaintConfigurationSinkMeta {
            override val message = id
            override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
        }
    }
    @Test fun `deferred global drop preserves the original ordered checks and canonical tail behavior`() {
        MethodAnalysisFixtures().use { f ->
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val field = f.field("f")
            val child = f.field("g")
            val t = f.mark("T")
            val mark = MarkSlot.Concrete(t)
            val both = f.manager.taintAlg.leafNode(f.manager.taintLeaves(MarkSet.of(t), MarkSet.of(t)))
            val input = f.manager.taintTree(STATIC, Layer.DEMAND,
                root = f.manager.taintAlg.prepend(f.manager, f.manager.path(intArrayOf(cls, field)), both),
                exclusion = ExclusionSet.Empty, anyTail = Tail.ANY)
            fun check(path: List<Int>) = SinkRule(rule("drop $path"), 0,
                listOf(f.pattern(STATIC, path, Tail.EXACT, mark)), emptyList())
            val checks = listOf(check(listOf(cls, field, child)), check(listOf(cls, field)))
            fun exit(sinks: List<SinkRule>) = ExitRules(RuleStatement(StatementSummary.EMPTY,
                StatementSummary.EMPTY, sinks), true, emptySet())
            val mode = ApMode(false, Direction.FORWARD, 2, MarkMode.FULL)
            val kept = assertNotNull(finishMethodData(f.ops, mode, f.manager.zero, input, exit(checks)))
            assertEquals(listOf(PathFact(STATIC, listOf(cls, field), Tail.EXACT, mark)),
                f.ops.leaves(kept).map { it.fact }.toList(),
                "Removing the last ANY branch canonicalizes its tail before the second original mask")
            assertNull(finishMethodData(f.ops, mode, f.manager.zero, input, exit(checks.reversed())),
                "The two original masks cannot be reordered or replaced by their union")
        }
    }

    @Test fun `entry mark removal uses the restored method origin rather than a local span initial`() {
        MethodAnalysisFixtures().use { f ->
            val argument = AccessPathBase.Argument(0)
            val t = f.mark("T")
            val u = f.mark("U")
            val value = f.fact(argument, emptyList(), Tail.EXACT, MarkSlot.Concrete(t))
            val input = f.manager.initial(f.pattern(argument, mark = MarkSlot.Concrete(u)))
            val exit = ExitRules(RuleStatement.EMPTY, false, setOf(t))
            val mode = ApMode(false, Direction.FORWARD, 2, MarkMode.FULL)
            assertNull(finishMethodData(f.ops, mode, f.manager.zero, value, exit))
            assertEquals(value, finishMethodData(f.ops, mode, input, value, exit))
            assertEquals(value, finishMethodData(f.ops, ApMode(true, Direction.FORWARD, 1, MarkMode.FULL),
                f.manager.zero, value, exit), "The existing run-1 exception stays unchanged")
        }
    }

    @Test fun `backward metadata does not add forward static sink removal`() {
        MethodAnalysisFixtures().use { f ->
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val field = f.field("f")
            val mark = MarkSlot.Concrete(f.mark("T"))
            val input = f.fact(STATIC, listOf(cls, field), Tail.EXACT, mark)
            val sink = SinkRule(rule("static CM"), 0,
                listOf(f.pattern(STATIC, listOf(cls, field), Tail.EXACT, mark)), emptyList())
            val exit = ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)),
                true, emptySet())
            assertEquals(input, finishMethodData(f.ops, ApMode(false, Direction.BACKWARD, 2, MarkMode.FULL),
                f.manager.zero, input, exit))
        }
    }
}
