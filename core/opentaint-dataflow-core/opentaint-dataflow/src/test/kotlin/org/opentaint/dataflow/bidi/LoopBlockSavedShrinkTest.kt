package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.RunConfig
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.MicroEdgeBuilder
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** Saved NORMAL transfer runs before current block admission. A shrinking row
 * must relay more than one iteration even when every local demand is empty. */
class LoopBlockSavedShrinkTest {
    private data class SavedOffer(val scope: BlockScope, val actual: Pattern)

    @Test fun `saved shrinking body repeats twice without current local demand and retains the whole original`() {
        MethodAnalysisFixtures(successors = listOf(
            listOf(1),        // 0 original entry
            listOf(2),        // 1 x=p
            listOf(3, 4),     // 2 loop header
            listOf(2),        // 3 x=x.f, then repeat
            listOf(5),        // 4 return x
            emptyList(),      // 5 original normal exit
            emptyList(),      // 6 unused exceptional exit
        ), normalExit = 5, exceptionalExit = 6).use { f ->
            val p = AccessPathBase.Argument(0)
            val x = AccessPathBase.LocalVar(0)
            val ret = AccessPathBase.Return
            val field = f.field("f")
            val mark = MarkSlot.Concrete(f.mark("T"))
            f.statement(1, MicroEdgeBuilder().apply { move(x, p) }.build())
            f.statement(3, MicroEdgeBuilder().apply { read(x, x, listOf(field)) }.build())
            f.statement(4, MicroEdgeBuilder().apply { move(ret, x) }.build())
            val layout = f.contexts.blockLayout(f.key)
            val top = layout[layout.root]
            val before = checkNotNull(top.before)
            val loop = checkNotNull(top.loop)
            val after = checkNotNull(top.after)
            val entry = PortId.ROOT_ENTRY
            val loopInput = checkNotNull(layout.port(1, 2)).id
            val repeat = checkNotNull(layout.port(3, 2)).id
            val leave = layout.normalExitForRoute(checkNotNull(layout.port(2, 4)).id)!!.id
            val normal = PortId.ROOT_EXIT
            assertEquals(listOf(repeat), layout[loop].repeatPorts)

            fun flow(base: AccessPathBase, path: List<Int> = emptyList()) =
                f.pattern(base, path, Tail.STAR, MarkSlot.STAR)
            fun saved(scope: BlockScope, exit: PortId, initial: Pattern, conclusion: Pattern) {
                // These relations are produced by the stated move/read/leave
                // transfers. They are legal F3 NORMAL records at field limit 2.
                f.records.add(Record(f.key, Direction.FORWARD, f.manager.initial(initial),
                    f.manager.factsOf(conclusion.fact, conclusion.exclusion, Layer.NORMAL), scope, exit))
            }
            saved(BlockScope(before, entry), loopInput, flow(p), flow(x))
            for (input in listOf(loopInput, repeat)) {
                saved(BlockScope(loop, input), repeat, flow(x, listOf(field)), flow(x))
                saved(BlockScope(loop, input), leave, flow(x), flow(x))
            }
            saved(BlockScope(after, leave), normal, flow(x), flow(ret))

            val incoming = f.pattern(p, listOf(field, field), Tail.EXACT, mark)
            val output = f.pattern(ret, tail = Tail.EXACT, mark = mark)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(incoming, output))
            }.build()
            val offered = ArrayList<SavedOffer>()
            val observedRecords = object : RecordStore by f.records {
                override fun byEntry(method: MethodKey, scope: BlockScope, addedFact: Pattern): Sequence<Record> {
                    offered += SavedOffer(scope, addedFact)
                    return f.records.byEntry(method, scope, addedFact)
                }
                override fun view(): RecordStore = this
            }
            val config = RunConfig(5, 4, demand, observedRecords, SeedIndex.EMPTY, listOf(f.key),
                run1MarkMode = MarkMode.FULL)
            val core = f.core(config)
            val actual = f.manager.factsOf(incoming.fact, incoming.exclusion, Layer.NORMAL)
            val admitted = demand.initials(f.key, actual, config.admissionPolicy)
            assertEquals(setOf(AdmittedInitial(f.manager.initial(incoming), Layer.NORMAL)), admitted)
            admitted.forEach(core::addInitial)
            f.drain(core)

            val repeatInputs = offered.filter { it.scope == BlockScope(loop, repeat) }
                .map { it.actual }.filter { it.fact.mark == mark }.toSet()
            assertContains(repeatInputs, f.pattern(x, listOf(field), Tail.EXACT, mark))
            assertContains(repeatInputs, f.pattern(x, tail = Tail.EXACT, mark = mark))
            assertTrue(repeatInputs.size >= 2,
                "The first saved traversal produces x.f/T; the next produces x.$/T")
            assertTrue(offered.any { it.scope == BlockScope(loop, loopInput) &&
                it.actual == f.pattern(x, listOf(field, field), Tail.EXACT, mark) })

            val retained = core.summaries.all().toList()
            assertEquals(1, retained.size)
            assertSame(admitted.single().initial, retained.single().first,
                "Two local repeats must retain the complete p.f.f/T parent original")
            assertEquals(Layer.NORMAL, retained.single().second.layer)
            assertEquals(listOf(output), f.ops.leaves(retained.single().second).toList(),
                "The exact paired exit rejects ret.f.f/T and ret.f/T and admits ret.$/T")
            assertTrue(core.summaries.demandEdges(Direction.FORWARD).none())
            assertTrue(f.processed.none { it.node.location.index in 1..4 },
                "With no local current demand, saved replay must finish without analyzing a child body")
            assertEquals(listOf(BlockScope.ROOT), core.joinedBlockStates().map { it.first },
                "A saved-only offer must not allocate mutable local state")
            core.freeze()
            assertTrue(core.blockSummaries().none())
            assertTrue(core.blockTargets().none())
        }
    }
}
