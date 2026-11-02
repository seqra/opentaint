package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*

class LoopBlockStaticReplyWorkTest {
    @Test fun `late static boundary answer reserves work when its child initial already exists`() {
        // C.f has an external FLOW writer. T is supplied only after this method is idle.
        // void m(Node p) {
        //   Node x;
        //   if (choose()) x = C.f; else x = p;
        //   while (again()) { /* a local CM(x,T) requests x/T below */ }
        // }
        val graph = listOf(listOf(1), listOf(2, 3), listOf(4), listOf(4),
            listOf(5), listOf(5, 6), emptyList())
        MethodAnalysisFixtures(graph, normalExit = 6).use { f ->
            val p = AccessPathBase.Argument(0)
            val x = AccessPathBase.LocalVar(0)
            val t = f.mark("T")
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val region = f.pattern(STATIC, path, Tail.STAR, MarkSlot.STAR)
            val operation = OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(2)))
            val read = starEdge(STATIC, path, x, emptyList())
            f.statement(2, MicroEdgeBuilder().apply {
                keepZero(); edge(read)
                staticOperation(StaticOperation.Read(operation, read))
            }.buildStage())
            f.statement(3, MicroEdgeBuilder().apply { move(x, p) }.build())
            val actor = f.core(RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key),
                run1MarkMode = MarkMode.FULL), localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val service = assertNotNull(actor.runnerPort.staticService)
            assertTrue(service.commit(StaticBatch().apply { writes += region }).isEmpty())
            actor.addRootZero()
            actor.addInitial(f.manager.initial(f.pattern(p, tail = Tail.STAR, mark = MarkSlot.Concrete(t))))
            f.drain(actor, quantum = 1)
            val runtime = assertNotNull(actor.blockRuntime)
            runtime.requireIdle()
            val loop = runtime.layout.ownerOf(5)
            val child = runtime.states().single { (scope, state) ->
                scope.block == loop && scope.entry !in runtime.layout[loop].repeatPorts &&
                    state.initials.all().any { it.base == x && it.mark is MarkSlot.Star }
            }.second
            val flowInitial = child.initials.all().single { it.base == x && it.mark is MarkSlot.Star }
            // The same request is answered by the p/T input first. The static
            // origin's answer arrives later, so C2 has no new child initial.
            child.addMarkRequest(flowInitial, t)
            f.drain(actor, quantum = 1)
            assertTrue(child.initials.all().any { it.base == x && it.mark == MarkSlot.Concrete(t) })
            assertTrue(runtime.states().any { (scope, _) ->
                var suppliedFlow = false
                actor.forEachJoinedLocalInput(scope) { link, input ->
                    if (link.original is InitialAp && link.original.member(0).base == STATIC && input is FlowTree)
                        suppliedFlow = true
                }
                suppliedFlow
            }, "The pending request must come from a real static-read local input")
            runtime.requireIdle()
            val answers = service.commit(StaticBatch().apply { supplies += RegionGroups(region, MarkSet.of(t)) })
                .filter { it.owner == actor.key }
            assertTrue(answers.any { it is StaticOwnerEffect.PointReady })
            var duplicateInitialWakeups = 0
            for (answer in answers) {
                val beforeInitials = runtime.states().sumOf { it.second.initials.all().size }
                f.enqueued.clear()
                actor.onStaticEffect(answer)
                val pending = runCatching { runtime.requireIdle() }.isFailure
                val afterInitials = runtime.states().sumOf { it.second.initials.all().size }
                if (pending && beforeInitials == afterInitials) {
                    duplicateInitialWakeups++
                    assertTrue(f.enqueued.any { it === actor },
                        "A reply queued local delivery without a fresh initial; it still needs counted method Work")
                }
                f.drain(actor, quantum = 1)
                runtime.requireIdle()
            }
            assertTrue(duplicateInitialWakeups > 0, "The control must exercise a late reply with unchanged child initials")
            actor.freeze()
            assertNull(actor.blockRuntime)
        }
    }
}
