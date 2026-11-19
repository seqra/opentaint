package org.opentaint.dataflow.bidi

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.ap.ExclusionSet
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.starEdge
import kotlin.test.*

/** Shows the effect of the selected admitted-MAY view, without a driver policy. */
class ProjectedMayCoverTest {
    @Test fun exactProbeDoesNotProveThatMayReadBranchIsCovered() {
        val f = StoreFixtures()
        val p = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val a = f.field("f"); val g = f.field("g"); val h = f.field("h")
        val t = MarkSlot.Concrete(f.mark("T"))
        val mode = ApMode(false, Direction.FORWARD, 4)
        fun pat(base: AccessPathBase, path: List<Int>, tail: Tail, mark: MarkSlot = MarkSlot.STAR) =
            Pattern(PathFact(base, path, tail, mark), ExclusionSet.Empty)
        fun facts(q: Pattern, layer: Layer) = f.manager.factsOf(q.fact, q.exclusion, layer)
        fun collect(body: (ApOut) -> Unit) = ArrayList<Facts>().also { rows ->
            body(object : ApOut {
                override fun result(value: Facts) { rows += value }
                override fun markRequest(mark: TaintMark) = error("No requests in a restricted AP test")
            })
        }
        fun leaves(rows: List<Facts>) = rows.flatMap { value ->
            f.ops.leaves(value).map { it to value.layer }.toList()
        }.toSet()
        val exact = pat(p,listOf(a),Tail.EXACT)
        val may = pat(p,listOf(a),Tail.ANY)
        val body = listOf(starEdge(p,listOf(a),ret,emptyList()),
            starEdge(p,listOf(a,g),ret,emptyList()))
        fun run(q: Pattern, layer: Layer) = collect { out ->
            for (edge in body) f.ops.applyEdge(facts(q,layer),f.manager.initial(q),edge,true,mode,out)
        }
        val exactResults = run(exact,Layer.NORMAL)
        assertEquals(setOf(pat(ret,emptyList(),Tail.EXACT) to Layer.NORMAL),leaves(exactResults))
        val strong = normalizeFlowSummary(f.manager,f.manager.initial(exact),exactResults.single())
        val weakResults = run(may,Layer.DEMAND)
        assertEquals(setOf(pat(ret,emptyList(),Tail.ANY) to Layer.DEMAND),leaves(weakResults))
        val actual = facts(pat(p,listOf(a,g),Tail.EXACT,t),Layer.NORMAL)
        val view = facts(pat(p,listOf(a),Tail.ANY,t),Layer.DEMAND)
        val strongResult = collect { out ->
            f.ops.applySummary(actual,strong.premise as InitialAp,strong.facts,mode,out)
        }
        val weakResult = collect { out ->
            f.ops.applySummary(view,f.manager.initial(may),weakResults.first(),mode,out)
        }
        assertEquals(setOf(pat(ret,listOf(g),Tail.EXACT,t) to Layer.NORMAL),leaves(strongResult))
        assertEquals(setOf(pat(ret,emptyList(),Tail.ANY,t) to Layer.DEMAND),leaves(weakResult))
        val root = pat(ret,emptyList(),Tail.EXACT,t)
        assertTrue(collect { out ->
            f.ops.applyEdge(actual,f.manager.initial(exact),body[1],true,mode,out)
        }.any { root in f.ops.leaves(it).toList() }, "The second ordinary branch really returns the root T")
        val longMay = facts(pat(p,listOf(a,g,h),Tail.ANY,t),Layer.DEMAND)
        val longStrong = collect { out ->
            f.ops.applySummary(longMay,strong.premise as InitialAp,strong.facts,mode,out)
        }
        assertEquals(setOf(pat(ret,listOf(g,h),Tail.ANY,t) to Layer.DEMAND),leaves(longStrong))
        val longPoint = facts(pat(p,listOf(a,g,h),Tail.EXACT,t),Layer.NORMAL)
        val realH = pat(ret,listOf(h),Tail.EXACT,t)
        assertTrue(collect { out ->
            f.ops.applyEdge(longPoint,f.manager.initial(exact),body[1],true,mode,out)
        }.any { realH in f.ops.leaves(it).toList() })

        // Replacing the MAY start with ordinary STAR (as in the new proposal)
        // preserves the other branch as an explicitly correlation-losing row.
        // No admitted MAY application view is needed for this counterexample.
        val star = pat(p,listOf(a),Tail.STAR)
        val starResults = run(star,Layer.NORMAL)
        val normalRows = starResults.filter { it.layer == Layer.NORMAL }
        val demandRows = starResults.filter { it.layer == Layer.DEMAND }
        assertEquals(setOf(pat(ret,emptyList(),Tail.STAR) to Layer.NORMAL),leaves(normalRows))
        assertEquals(setOf(pat(ret,emptyList(),Tail.ANY) to Layer.DEMAND),leaves(demandRows))
        val starNormalApplication = collect { out ->
            for (row in normalRows) f.ops.applySummary(actual,f.manager.initial(star),row,mode,out)
        }
        val starDemandApplication = collect { out ->
            for (row in demandRows) f.ops.applySummary(actual,f.manager.initial(star),row,mode,out)
        }
        assertEquals(setOf(pat(ret,listOf(g),Tail.EXACT,t) to Layer.NORMAL),leaves(starNormalApplication))
        assertEquals(setOf(pat(ret,emptyList(),Tail.ANY,t) to Layer.DEMAND),leaves(starDemandApplication))
        assertFalse(root in leaves(starNormalApplication).map { it.first })
    }
}
