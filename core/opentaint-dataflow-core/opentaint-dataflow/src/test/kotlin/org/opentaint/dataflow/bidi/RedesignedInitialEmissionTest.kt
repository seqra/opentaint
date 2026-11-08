package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.MicroEdgeBuilder
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Selected C2/C5 contract. Expected commands are literal spec cells, not a second emitter. */
class RedesignedInitialEmissionTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val p = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return
    private val a = f.field("a")
    private val b = f.field("b")
    private val c = f.field("c")
    private val t = MarkSlot.Concrete(f.mark("T"))
    private val u = MarkSlot.Concrete(f.mark("U"))
    private fun pat(path: List<Int> = emptyList(), tail: Tail = Tail.STAR, mark: MarkSlot = t,
                    base: AccessPathBase = p, e: ExclusionSet = ExclusionSet.Empty) =
        Pattern(PathFact(base, path, tail, mark), e)
    private fun policy(run: Int = 3, limit: Int = 3) = RestrictedInitialPolicy(run, limit,
        if (run % 2 == 0) Direction.BACKWARD else Direction.FORWARD, ap.marks)
    private fun admission(pattern: Pattern, layer: Layer) = InitialEmission(pattern, layer)

    @Test fun `same-head MAY accepts STAR and MAY as a STAR identity without a prefix command`() {
        for (run in listOf(2,3,4,5)) for (actualTail in listOf(Tail.STAR, Tail.ANY)) {
            val actual = pat(tail = actualTail)
            assertEquals(listOf(admission(pat(), Layer.DEMAND),
                admission(pat(mark = MarkSlot.STAR), Layer.NORMAL)),
                policy(run).emitAdmissions(pat(tail = Tail.ANY), actual, Layer.DEMAND))
            assertEquals(listOf(admission(pat(mark = MarkSlot.STAR), Layer.NORMAL)),
                policy(run).emitAdmissions(pat(tail = Tail.ANY, mark = MarkSlot.STAR), actual, Layer.DEMAND))
        }
    }

    @Test fun `first-field concrete STAR has both FLOW companions and preserves the submitted packet`() {
        val input = pat(listOf(a,b), Tail.EXACT)
        val demand = pat(tail = Tail.ANY)
        val expected = listOf(admission(pat(listOf(a)), Layer.DEMAND),
            admission(pat(listOf(a), mark = MarkSlot.STAR), Layer.NORMAL),
            admission(pat(tail = Tail.EXACT, mark = MarkSlot.STAR), Layer.NORMAL))
        val results = policy().emitAdmissions(demand, input, Layer.NORMAL)
        assertEquals(expected, results)
        val store = DemandStore.Builder(ap).apply {
            add(f.method, DemandPattern(demand, pat(base = ret, tail = Tail.ANY)))
        }.build()
        val offered = ap.factsOf(input.fact, input.exclusion, Layer.NORMAL)
        assertEquals(expected.map { AdmittedInitial(ap.initial(it.pattern), it.layer) }.toSet(),
            store.initials(f.method, offered, policy()))
        assertEquals(listOf(input), f.ops.leaves(offered).toList())
        assertTrue(results.none { it.pattern.fact.tail == Tail.ANY })
    }

    @Test fun `concrete exact one-field exception gets only the exact FLOW prefix`() {
        val input = pat(listOf(a), Tail.EXACT)
        assertEquals(listOf(admission(input,Layer.NORMAL),
            admission(pat(tail=Tail.EXACT,mark=MarkSlot.STAR),Layer.NORMAL)),
            policy().emitAdmissions(pat(tail=Tail.ANY),input,Layer.NORMAL))
        assertEquals(listOf(admission(input,Layer.DEMAND),
            admission(pat(tail=Tail.EXACT,mark=MarkSlot.STAR),Layer.NORMAL)),
            policy().emitAdmissions(pat(tail=Tail.ANY),input,Layer.DEMAND))
    }

    @Test fun `rejected primaries never get companion commands`() {
        val q = policy()
        assertTrue(q.emitAdmissions(pat(listOf(a),Tail.EXACT),pat(),Layer.DEMAND).isEmpty())
        assertTrue(q.emitAdmissions(pat(listOf(a),Tail.ANY),pat(),Layer.NORMAL).isEmpty())
        assertTrue(q.emitAdmissions(pat(tail=Tail.ANY,mark=u),pat(listOf(a),Tail.EXACT),Layer.NORMAL).isEmpty())
        assertTrue(q.emitAdmissions(pat(),pat(listOf(a),Tail.EXACT),Layer.NORMAL).isEmpty())
        assertTrue(q.emitAdmissions(pat(listOf(a),Tail.ANY),
            pat(tail=Tail.ANY_TAINT,e=ExclusionSet.of(a)),Layer.NORMAL).isEmpty())
    }

    @Test fun `coverage waits for every command in the full family`() {
        val actual = pat(listOf(a,b),Tail.EXACT)
        val target = pat(tail=Tail.ANY)
        val results = InitialDemandResults(ap,policy(),Layer.NORMAL)
        results.requireFamily(target,false,actual)
        results.offer(pat(listOf(a),Tail.ANY),actual) // Same primary; prefix is at a, not at p.
        assertFalse(results.has(target,actual))
        assertFalse(results.fullyCovered)
        results.offer(target,actual)
        assertTrue(results.has(target,actual))
        assertTrue(results.fullyCovered)
        assertTrue(results.initials.none { it.initial.tail == Tail.ANY })
    }

    @Test fun `C5 authorizes a concrete STAR companion without marking an excluded T output`() {
        val q = policy(4,3)
        val dc = pat(tail=Tail.ANY)
        val start = pat(listOf(a),mark=MarkSlot.STAR)
        assertTrue(q.canStoreInitial(dc,start))
        assertFalse(q.canStoreInitial(dc,start.copy(fact=start.fact.copy(mark=MarkSlot.Star(ap.markSetOf(u.mark))))),
            "A companion FLOW initial has empty mx")
        assertFalse(q.canEmitInitial(dc,start),"The public companion is not a concrete primary")
        val store = DemandStore.Builder(ap).apply {
            add(f.method,DemandPattern(dc,pat(base=ret,tail=Tail.ANY)))
        }.build()
        val initial = ap.initial(start)
        val raw = ap.factsOf(pat(base=ret,mark=MarkSlot.STAR).fact,ExclusionSet.Empty,Layer.NORMAL)
        assertEquals(listOf(raw),store.intersect(f.method,initial,raw,q))
        val excluded = ap.factsOf(pat(base=ret,mark=MarkSlot.Star(ap.markSetOf(t.mark))).fact,
            ExclusionSet.Empty,Layer.NORMAL)
        assertTrue(store.intersect(f.method,initial,excluded,q).isEmpty())
        val prepared = assertNotNull(store.prepareDataPlan(f.method,listOf(start),q))
        assertEquals(store.intersect(f.method,initial,raw,q),prepared.intersect(initial,raw))
        assertTrue(assertNotNull(prepared.intersect(initial,excluded)).isEmpty())
    }

    @Test fun `paired C5 keeps both a precise normal output and a separate cut output`() {
        val q = policy(4,3)
        val start = pat(listOf(a),mark=MarkSlot.STAR)
        val store = DemandStore.Builder(ap).apply {
            add(f.method,DemandPattern(pat(tail=Tail.ANY),pat(listOf(a),Tail.STAR,base=ret)))
            add(f.method,DemandPattern(pat(tail=Tail.ANY),pat(tail=Tail.ANY,base=ret)))
        }.build()
        val initial=ap.initial(start)
        val result=pat(listOf(a,b),mark=MarkSlot.STAR,base=ret)
        val raw=ap.factsOf(result.fact,result.exclusion,Layer.NORMAL)
        val expected=setOf(Conclusion(result.fact,ExclusionSet.Empty,false),
            Conclusion(pat(listOf(a),Tail.ANY,MarkSlot.STAR,ret).fact,ExclusionSet.Empty,true))
        fun decode(values:List<Facts>)=values.flatMap { value -> f.ops.leaves(value).map {
            Conclusion(it.fact,it.exclusion,value.layer==Layer.DEMAND)
        }.toList() }.toSet()
        assertEquals(expected,decode(store.intersect(f.method,initial,raw,q)))
        val prepared=assertNotNull(store.prepareDataPlan(f.method,listOf(start),q))
        assertEquals(expected,decode(assertNotNull(prepared.intersect(initial,raw))))
    }

    @Test fun `exact FLOW prefix records a child write exclusion before whole-summary normalization`() {
        MethodAnalysisFixtures(listOf(listOf(1),listOf(2),listOf(3),emptyList()),3).use { method ->
            val field=method.field("written")
            val suffix=method.field("suffix")
            val mark=MarkSlot.Concrete(method.mark("T"))
            val tmp=AccessPathBase.LocalVar(9)
            method.statement(1,MicroEdgeBuilder().apply {
                write(p,listOf(field),false,listOf(tmp),emptyList())
            }.build())
            method.statement(2,MicroEdgeBuilder().apply { move(ret,p) }.build())
            val demand=DemandStore.Builder(method.manager).apply {
                add(method.key,DemandPattern(pat(tail=Tail.ANY,mark=mark),
                    pat(base=ret,tail=Tail.ANY,mark=mark)))
            }.build()
            val actor=method.core(index=3,L=2,demand=demand)
            val actual=method.fact(p,listOf(field,suffix),Tail.EXACT,mark)
            method.submitRestricted(actor,actual)
            method.drain(actor)
            val rows=actor.summaries.all().flatMap { (initial,value) ->
                method.ops.leaves(value).map { Triple((initial as InitialAp).toPattern(),it,value.layer) }
            }.filter { it.second.fact.base==ret }.toList()
            assertEquals(listOf(Triple(pat(mark=MarkSlot.STAR),
                pat(mark=MarkSlot.STAR,base=ret,e=ExclusionSet.of(field)),Layer.NORMAL)),rows)
        }
    }

    @Test fun `finite primary image has executable witnesses and cannot contain MAY`() {
        val paths=listOf(emptyList(),listOf(a),listOf(b),listOf(a,a),listOf(a,b),listOf(b,a),listOf(b,b))
        for(run in listOf(2,3)) {
            val q=policy(run,2)
            val actuals=paths.flatMap { path -> Tail.entries.flatMap { tail ->
                listOf(MarkSlot.STAR,t,u).map { pat(path,tail,it) }
            } }
            val demands=actuals.filter { it.fact.tail!=Tail.ANY_TAINT }
            for(demand in demands) {
                val image=actuals.mapNotNull { q.emit(demand,it) }.toSet()
                assertTrue(image.none { it.fact.tail==Tail.ANY })
                for(candidate in actuals) assertEquals(candidate in image,q.canEmitInitial(demand,candidate),
                    "run=$run demand=$demand candidate=$candidate")
            }
        }
    }
}
