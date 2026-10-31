package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.starEdge
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*

/** Proposal control only. Not installed or run during the project campaign.
 * Code under analysis: Object m(Box p) { return p.a.b.c.d; }
 * Backward run-4 / limit3 summary cuts the four-field return image to p.a.b.c.[any]. */
class ReturnImageCollapseTest {
    @Test
    fun `two eligible input headers survive N2 admission but collapse to one summary image`() {
        MethodAnalysisFixtures().use { f ->
            val returned = AccessPathBase.Return
            val argument = AccessPathBase.Argument(0)
            val field = f.field("f")
            val abc = listOf(f.field("a"), f.field("b"), f.field("c"))
            val t = MarkSlot.Concrete(f.mark("T"))
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(f.pattern(returned, tail = Tail.ANY, mark = MarkSlot.STAR), null))
            }.build()
            val config = f.config(index = 4, demand = demand)
            val actuals = listOf(Tail.EXACT, Tail.ANY).map { tail ->
                f.fact(returned, listOf(field), tail, t, layer = Layer.DEMAND)
            }
            assertNotEquals(actuals[0].groupKey, actuals[1].groupKey)
            val initials = actuals.map { emitRestrictedInitials(config, f.ops, f.key, it).single() }
            assertSame(initials[0], initials[1])
            assertEquals(f.pattern(returned, listOf(field), Tail.STAR, MarkSlot.STAR), initials[0].toPattern())
            val ref = CallerRef(f.store.key("caller"), f.manager.zero, Layer.DEMAND, f.inst(1), 0)
            val directory = CalleeSubscriptions(f.ops)
            val inputs = actuals.map { Subscription(f.key, ref, it.layer, it) }
            assertNotNull(directory.add(inputs[0]))
            assertNotNull(directory.add(inputs[1]), "Existing input dedup must keep these distinct headers")
            val pub = Publication(initials[0], f.fact(argument, abc, Tail.ANY, MarkSlot.STAR, layer = Layer.DEMAND))
            val images = inputs.map { part ->
                val matched = assertNotNull(matches(part, pub, 0, f.ops, config.mode))
                val out = CollectingOut()
                f.ops.applySummary(matched, pub.premise as InitialAp, pub.conclusion, config.mode, out,
                    original = part.ref.premise)
                assertTrue(out.markRequests.isEmpty())
                out.results.single()
            }
            assertEquals(images[0], images[1])
            assertEquals(listOf(f.pattern(argument, abc, Tail.ANY, t)), f.ops.leaves(images[0]).toList())
            assertEquals(Layer.DEMAND, images[0].layer)
            val callerArgument = AccessPathBase.LocalVar(99)
            val old = images.flatMap { image ->
                val out = CollectingOut()
                f.ops.applyEdge(image, ref.premise, starEdge(argument, emptyList(), callerArgument, emptyList()),
                    statementEdge = false, mode = config.mode, out = out)
                out.results.flatMap { f.ops.leaves(it).toList() }
            }.toSet()
            val once = CollectingOut()
            f.ops.applyEdge(images[0], ref.premise, starEdge(argument, emptyList(), callerArgument, emptyList()),
                statementEdge = false, mode = config.mode, out = once)
            assertEquals(old, once.results.flatMap { f.ops.leaves(it).toList() }.toSet())
            // Operation count for this finite example: two return suffix entries become one.
            assertEquals(2, images.size)
            assertEquals(1, images.toSet().size)
            directory.clear()
        }
    }
}
