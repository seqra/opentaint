package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.MicroEdgeBuilder
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class LoopBlockExternalHeaderTest {
    @Test fun `growing saved inner output uses empty AL and the actual enclosing repeat demand`() {
        // outer: while (a()) {
        //   do { x.f=x; if (c()) continue outer; } while (b());
        //   afterInner();
        // }
        // Only existing CFG paths are used. A supplied NORMAL saved write is
        // the actual x.f.* -> x.f.f.* relation at instruction 2.
        MethodAnalysisFixtures(listOf(listOf(1), listOf(2, 8), listOf(3, 4, 5),
            listOf(2), listOf(6), listOf(1), listOf(1), emptyList(), emptyList(), emptyList()),
            normalExit = 8, exceptionalExit = 9).use { f ->
            val x = AccessPathBase.Argument(0)
            val field = f.field("f")
            val mark = MarkSlot.Concrete(f.mark("T"))
            f.statement(2, MicroEdgeBuilder().apply {
                write(x, listOf(field), weak = false, values = listOf(x), aliasPaths = emptyList())
            }.build())
            val layout = f.contexts.blockLayout(f.key)
            val top = layout[layout.root]
            val outer = layout[checkNotNull(top.loop)]
            val inner = layout[checkNotNull(outer.loop)]
            val outerInput = layout.port(0, 1)!!.id
            val innerInput = layout.port(1, 2)!!.id
            val outerRepeat = listOf(layout.port(5, 1)!!.id, layout.port(6, 1)!!.id)
            val outerNormal = layout.normalExits.single { it.loop == outer.id }.id
            val innerNormal = layout.normalExits.single { it.loop == inner.id }.id
            assertEquals(1, layout.normalExit(innerNormal)!!.target)
            assertTrue(layout[checkNotNull(outer.after)].instructions.isEmpty())
            fun flow(path: List<Int> = emptyList()) = f.pattern(x, path, Tail.STAR, MarkSlot.STAR)
            fun saved(scope: BlockScope, exit: PortId, initial: Pattern = flow(), result: Pattern = flow()) {
                f.records.add(Record(f.key, Direction.FORWARD, f.manager.initial(initial),
                    f.manager.factsOf(result.fact, result.exclusion, Layer.NORMAL), scope, exit))
            }
            saved(BlockScope(checkNotNull(top.before), PortId.ROOT_ENTRY), outerInput)
            saved(BlockScope(checkNotNull(outer.before), outerInput), innerInput)
            saved(BlockScope(checkNotNull(outer.before), outerInput), outerNormal)
            saved(BlockScope(inner.id, innerInput), innerNormal, flow(listOf(field)), flow(listOf(field, field)))
            saved(BlockScope(checkNotNull(outer.after), innerNormal), innerNormal)
            for (repeat in outerRepeat) saved(BlockScope(outer.id, repeat), outerNormal)
            saved(BlockScope(checkNotNull(top.after), outerNormal), PortId.ROOT_EXIT)
            val provided = f.pattern(x, listOf(field), Tail.EXACT, mark)
            val needed = f.pattern(x, listOf(field, field), Tail.ANY, mark)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(provided, needed))
                for (repeat in outerRepeat) add(f.key, BlockScope(outer.id, outerInput), repeat,
                    DemandPattern(provided, needed))
            }.build()
            val actor = f.core(index = 5, L = 4, demand = demand)
            val submitted = f.manager.factsOf(provided.fact, provided.exclusion, Layer.NORMAL)
            f.submitRestricted(actor, submitted)
            f.drain(actor, quantum = 1)
            val expected = f.pattern(x, listOf(field, field), Tail.EXACT, mark)
            val retained = actor.summaries.all().toList()
            if (retained.isEmpty()) println(buildString {
                val runtime = assertNotNull(actor.blockRuntime)
                appendLine("EXTERNAL_HEADER_TRACE ${runtime.diagnosticStatistics()}")
                for ((scope, state) in runtime.states()) {
                    appendLine("scope=$scope initials=${state.initials.all().map { it.toPattern() }}")
                    for ((exit, rows) in state.portSummaries.entries()) for ((origin, image) in rows.all())
                        appendLine("scope=$scope exit=$exit ${origin.members.map { it.toPattern() }} -> ${f.ops.leaves(image).toList()} layer=${image.layer}")
                }
                for (event in f.processed) appendLine("processed=${event.node.location.index} ${event.premise} -> ${event.facts}")
            })
            assertTrue(retained.any { (original, value) -> original == f.manager.initial(provided) &&
                value.layer == Layer.NORMAL && expected in f.ops.leaves(value).toList()
            }, "The growing inner result must survive its AL identity and both real parent repeat demand pairs")
            val runtime = assertNotNull(actor.blockRuntime)
            val parent = runtime.state(BlockScope(outer.id, outerInput))
            for (repeat in outerRepeat) assertTrue(parent.portSummaries.entries().any { (exit, rows) ->
                exit == repeat && rows.all().any { (original, value) ->
                    original == f.manager.initial(provided) && value.layer == Layer.NORMAL &&
                        expected in f.ops.leaves(value).toList()
                }
            }, "The inner normal interface must restore the actual enclosing repeat $repeat")
            assertTrue(f.processed.isEmpty(), "Every executed span in this control is covered by a genuine saved NORMAL row")
            assertTrue(runtime.diagnosticStatistics().contains("drops=0"))
            actor.freeze()
        }
    }
}
