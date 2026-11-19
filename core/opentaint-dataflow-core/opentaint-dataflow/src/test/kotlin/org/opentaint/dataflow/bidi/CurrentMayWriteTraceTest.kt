package org.opentaint.dataflow.bidi

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.ap.ExclusionSet
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.starEdge
import kotlin.test.*

/** Native AP/C2/C5 trace of the current implementation; no proposed tail. */
class CurrentMayWriteTraceTest {
    @Test fun traceReadThenWriteUnderExactExitDemand() {
        val fx = StoreFixtures()
        val p = AccessPathBase.Argument(1)
        val x = AccessPathBase.Argument(0)
        val y = AccessPathBase.LocalVar(0)
        val g = fx.field("g")
        val f = fx.field("f")
        val t = MarkSlot.Concrete(fx.mark("T"))
        val mode = ApMode(false, Direction.FORWARD, 2)
        val policy = RestrictedInitialPolicy(3, 2, Direction.FORWARD, fx.manager.marks)
        fun pat(base: AccessPathBase, path: List<Int>, tail: Tail, mark: MarkSlot = t) =
            Pattern(PathFact(base,path,tail,mark),ExclusionSet.Empty)
        fun collect(body: (ApOut) -> Unit) = ArrayList<Facts>().also { result ->
            body(object : ApOut {
                override fun result(value: Facts) { result += value }
                override fun markRequest(mark: TaintMark) = error("No restricted requests")
            })
        }
        fun leaves(values: List<Facts>) = values.flatMap { value ->
            fx.ops.leaves(value).map { it to value.layer }.toList()
        }.toSet()
        val pair = DemandPattern(pat(p,emptyList(),Tail.ANY),pat(x,listOf(f),Tail.EXACT))
        val offered = pat(p,emptyList(),Tail.ANY)
        val emissions = policy.emitAdmissions(pair.entry,offered,Layer.DEMAND)
        assertEquals(setOf(
            InitialEmission(pat(p,emptyList(),Tail.STAR),Layer.DEMAND),
            InitialEmission(pat(p,emptyList(),Tail.STAR,MarkSlot.STAR),Layer.NORMAL)
        ),emissions.toSet())
        for (emission in emissions) {
            val initial = fx.manager.initial(emission.pattern)
            val start = fx.ops.startFact(initial,mode)
            assertEquals(emission.layer,start.layer)
            val read = collect { out ->
                fx.ops.applyEdge(start,initial,starEdge(p,listOf(g),y,emptyList()),true,mode,out)
            }
            val writes = read.flatMap { input -> collect { out ->
                fx.ops.applyEdge(input,initial,starEdge(y,emptyList(),x,listOf(f)),true,mode,out)
            } }
            val mark = emission.pattern.fact.mark
            assertEquals(setOf(pat(y,emptyList(),Tail.ANY,mark) to Layer.DEMAND),leaves(read))
            assertEquals(setOf(pat(x,listOf(f),Tail.ANY,mark) to Layer.DEMAND),leaves(writes))
            val bounded = writes.flatMap { input -> collect { fx.ops.limit(input,2,it) } }
            assertEquals(leaves(writes),leaves(bounded),"The known f is within the limit")
            val restricted = bounded.flatMap { fx.ops.restrict(initial,it,pair,policy) }
            val expectedTail = if (mark is MarkSlot.Star) Tail.STAR else Tail.EXACT
            assertEquals(setOf(pat(x,listOf(f),expectedTail,mark) to Layer.DEMAND),leaves(restricted))
        }
        // An actual marked root at y is a valid binding of its MAY fact.
        val exactY = fx.manager.factsOf(pat(y,emptyList(),Tail.EXACT).fact,ExclusionSet.Empty,Layer.NORMAL)
        val exactWrite = collect { out ->
            fx.ops.applyEdge(exactY,fx.manager.initial(pat(p,listOf(g),Tail.EXACT)),
                starEdge(y,emptyList(),x,listOf(f)),true,mode,out)
        }
        assertEquals(setOf(pat(x,listOf(f),Tail.EXACT) to Layer.NORMAL),leaves(exactWrite))
    }
}
