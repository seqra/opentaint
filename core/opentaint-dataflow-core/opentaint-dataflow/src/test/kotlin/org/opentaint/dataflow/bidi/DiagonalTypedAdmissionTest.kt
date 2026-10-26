package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.DiagonalRelations
import org.opentaint.dataflow.bidi.store.FlowBackedSummaries
import kotlin.test.*

/** Cross-header admission uses the selected TaintGroup law, including flags.
 * The oracle is intentionally not another DiagonalRelations instance. */
class DiagonalTypedAdmissionTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val t = fixture.mark("T")
    private val u = fixture.mark("U")
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val h = fixture.field("h")
    private val shape = m.initial(AccessPathBase.Argument(0), null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)
    private fun initial(mark: TaintMark = t, path: List<Int> = emptyList()) =
        m.initial(shape.base, m.path(path), shape.tail, shape.exclusion, MarkSlot.Concrete(mark))
    private fun facts(tail: Tail, paths: List<List<Int>> = listOf(listOf(f)), flagPaths: List<List<Int>> = emptyList(),
                      exclusion: ExclusionSet = ExclusionSet.Empty, mark: TaintMark = t,
                      layer: Layer = Layer.DEMAND, base: AccessPathBase = AccessPathBase.Return): TaintTree {
        fun root(paths: List<List<Int>>): TaintNode? = paths.map { p ->
            m.taintAlg.prepend(m, m.path(p), m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY,m.markSetOf(mark))))
        }.reduceOrNull { a,b -> m.taintAlg.mergeAdd(a,b,m.cancellation) }
        return m.taintTree(base,layer,checkNotNull(root(paths)),exclusion,tail,root(flagPaths))
    }
    private fun protected(tail: Tail, path: List<Int> = listOf(f), e: ExclusionSet = ExclusionSet.Empty) =
        facts(tail,listOf(path),listOf(path),e)
    private fun packet(facts: TaintTree, marks: MarkSet = m.markSetOf(t)): DiagonalDelta {
        check(facts.nonSubsumable == null || facts.nonSubsumable == facts.root)
        val geometry = fixture.ops.leaves(facts).map { p ->
            FlowAlgebra.prepend(m,m.path(p.fact.path),FlowAlgebra.LEAF_NODE)
        }.reduce { a,b -> FlowAlgebra.mergeAdd(a,b,m.cancellation) }
        return DiagonalDelta(shape,facts.base,facts.layer,geometry,marks,facts.nonSubsumable != null,facts.anyTail,facts.exclusion)
    }
    private fun scalar(packet: DiagonalDelta): List<Pair<InitialAp,TaintTree>> = packet.marks.ids.map { id ->
        val mark = TaintMark(id)
        val leaves = mutableListOf<TaintNode>()
        fun walk(n: FlowNode, path: List<Int>) {
            if (!n.leaf.isEmpty) leaves += m.taintAlg.prepend(m,m.path(path),
                m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY,m.markSetOf(mark))))
            n.accessorData?.forEachIndexed { index, accessor -> walk(n.childData!![index],path+accessor) }
        }
        walk(packet.geometry,emptyList())
        val root = leaves.reduce { a,b -> m.taintAlg.mergeAdd(a,b,m.cancellation) }
        initial(mark) to m.taintTree(packet.base,packet.layer,root,packet.exclusion,packet.tail,
            if(packet.protected)root else null)
    }
    private fun observe(values: Sequence<Facts>): Pair<Set<Pattern>,Set<Pattern>> {
        val current = values.toList()
        return current.flatMap { fixture.ops.leaves(it).toList() }.toSet() to current.flatMap { f ->
            (f as? TaintTree)?.protectedPart()?.let { fixture.ops.leaves(it).toList() }.orEmpty()
        }.toSet()
    }
    private fun parity(sequence: List<TaintTree>, usePackets: Boolean) {
        val oracle = TaintGroup(m,m.newInterners().taint)
        val store = DiagonalRelations(m)
        for ((step,offered) in sequence.withIndex()) {
            val expected = listOfNotNull(oracle.add(offered))
            val actual = if(usePackets && (offered.nonSubsumable == null || offered.nonSubsumable == offered.root)) {
                val value = packet(offered)
                val before = observe(store.all().map { it.second })
                val census = store.census()
                store.addDiagonal(value)?.flatMap { scalar(it).map { it.second } } ?: run {
                    assertEquals(before,observe(store.all().map { it.second }),"Fallback must precede mutation")
                    assertEquals(census,store.census(),"Fallback must precede mask mutation")
                    scalar(value).mapNotNull { (key,facts) -> store.add(key,facts) }
                }
            } else listOfNotNull(store.add(initial(),offered))
            assertEquals(observe(expected.asSequence()),observe(actual.asSequence()),"delta at step $step packets=$usePackets")
            assertEquals(observe(oracle.all()),observe(store.all().map { it.second }),"state at step $step packets=$usePackets")
        }
    }
    @Test fun `stored ANY suppresses later STAR with ordinary and protected admission gates`() {
        for(packets in listOf(false,true)) for(anyFlag in listOf(false,true)) for(starFlag in listOf(false,true)) {
            val any=if(anyFlag)protected(Tail.ANY)else facts(Tail.ANY)
            val star=if(starFlag)protected(Tail.STAR)else facts(Tail.STAR)
            parity(listOf(any,star,star,any),packets)
        }
    }
    @Test fun `STAR before ANY stays nonminimal and repeated offers terminate`() {
        for(packets in listOf(false,true)) for(starFlag in listOf(false,true)) for(anyFlag in listOf(false,true)) {
            val star=if(starFlag)protected(Tail.STAR)else facts(Tail.STAR)
            val any=if(anyFlag)protected(Tail.ANY)else facts(Tail.ANY)
            parity(listOf(star,any,any,star),packets)
        }
    }
    @Test fun `ANY prefix covers STAR descendants and preserves late protected obligations`() {
        for(packets in listOf(false,true)) {
            val child=protected(Tail.STAR,listOf(f,g))
            parity(listOf(protected(Tail.ANY),child,child),packets)
            parity(listOf(facts(Tail.ANY),facts(Tail.STAR),protected(Tail.STAR),protected(Tail.STAR)),packets)
        }
    }
    @Test fun `partial cross-header flags and ordinary geometry use independent subtraction`() {
        val any=facts(Tail.ANY,listOf(listOf(f),listOf(g)),listOf(listOf(g)))
        val star=facts(Tail.STAR,listOf(listOf(f),listOf(g),listOf(h)),listOf(listOf(g),listOf(h)))
        parity(listOf(any,star,star),false)
        val onlyF=facts(Tail.ANY)
        val partial=facts(Tail.STAR,listOf(listOf(f),listOf(g)),listOf(listOf(f)))
        parity(listOf(onlyF,partial,partial),false)
        // Uniform packets form the same partly protected mixed geometry.
        parity(listOf(facts(Tail.ANY),protected(Tail.ANY,listOf(g)),
            facts(Tail.STAR),protected(Tail.STAR,listOf(g)),protected(Tail.STAR,listOf(h)),
            protected(Tail.STAR,listOf(h))),true)
    }
    @Test fun `STAR exclusions cover and merge exactly as scalar admission in both orders`() {
        val eg=ExclusionSet.of(g)
        val eh=ExclusionSet.of(h)
        for(packets in listOf(false,true)) {
            parity(listOf(protected(Tail.STAR),protected(Tail.STAR,e=eg),protected(Tail.STAR,e=eg)),packets)
            parity(listOf(protected(Tail.STAR,e=eg),protected(Tail.STAR),protected(Tail.STAR)),packets)
            parity(listOf(protected(Tail.STAR,e=eg),protected(Tail.STAR,e=eh),protected(Tail.STAR,e=eh)),packets)
            parity(listOf(facts(Tail.STAR,exclusion=eg),protected(Tail.STAR,e=eh),protected(Tail.STAR,e=eh)),packets)
            parity(listOf(protected(Tail.STAR),protected(Tail.STAR,listOf(f,g),eg)),packets)
        }
    }
    @Test fun `mixed mark packet fallback is atomic and preserves its uncovered mark`() {
        for(anyFlag in listOf(false,true)) for(packetFlag in listOf(false,true)) {
            val store=DiagonalRelations(m)
            store.add(initial(),if(anyFlag)protected(Tail.ANY)else facts(Tail.ANY))
            val offered=packet(if(packetFlag)protected(Tail.STAR)else facts(Tail.STAR),
                m.intern(MarkSet(intArrayOf(t.id,u.id))))
            val before=store.census()
            assertNull(store.addDiagonal(offered))
            assertEquals(before,store.census())
            val deltas=scalar(offered).mapNotNull { (key,facts) -> store.add(key,facts)?.let { key to it } }
            val expected=if(packetFlag && !anyFlag)listOf(t,u)else listOf(u)
            assertEquals(expected,deltas.map { ((it.first.mark)as MarkSlot.Concrete).mark })
            assertEquals(1+expected.size.toLong(),store.census().concreteOutputMemberships)
        }
    }
    @Test fun `different initial base layer and output scope do not acquire cross-coverage`() {
        val store=DiagonalRelations(m)
        store.add(initial(),facts(Tail.ANY))
        assertNotNull(store.add(initial(path=listOf(g)),facts(Tail.STAR)))
        assertNotNull(store.add(initial(),facts(Tail.STAR,layer=Layer.NORMAL)))
        assertNotNull(store.add(initial(),facts(Tail.STAR,base=AccessPathBase.Argument(1))))
        assertEquals(4,store.census().concreteOutputMemberships)
    }
    @Test fun `summary owner uses the same cross-header admission without changing FLOW tail gates`() {
        val owner=FlowBackedSummaries(m)
        owner.add(initial(),facts(Tail.ANY))
        assertNull(owner.add(initial(),facts(Tail.STAR)))
        assertNotNull(owner.add(initial(),protected(Tail.STAR)))
        assertNull(owner.add(initial(),protected(Tail.STAR)))
        val other=FlowBackedSummaries(m)
        val flow=m.flowTree(AccessPathBase.Return,Layer.DEMAND,ExclusionSet.Empty,MarkSet.EMPTY,
            FlowAlgebra.prepend(m,m.path(listOf(f)),FlowAlgebra.LEAF_NODE),Tail.ANY)
        other.add(shape,flow)
        assertNotNull(other.add(initial(),facts(Tail.STAR)),"FLOW ANY must not gain a cross-tail TAINT replacement")
    }
    @Test fun `rewriting one atom preserves other shared geometry exclusions and protection`() {
        val eg=ExclusionSet.of(g)
        val eh=ExclusionSet.of(h)
        for(sharedFlag in listOf(false,true)) {
            val store=DiagonalRelations(m)
            val shared=if(sharedFlag)protected(Tail.STAR,e=eg)else facts(Tail.STAR,exclusion=eg)
            assertNotNull(store.addDiagonal(packet(shared,m.intern(MarkSet(intArrayOf(t.id,u.id))))))
            val beforeU=observe(store.borrow(initial(u)))
            val update=protected(Tail.STAR,e=eh)
            val before=store.census()
            assertNull(store.addDiagonal(packet(update)))
            assertEquals(before,store.census())
            val delta=assertNotNull(store.add(initial(),update))
            assertEquals(ExclusionSet.Empty,(delta as TaintTree).exclusion)
            assertEquals(beforeU,observe(store.borrow(initial(u))))
            assertEquals(2,store.census().concreteOutputMemberships)
            assertNull(store.add(initial(),update))
        }
    }
    @Test fun `FLOW compaction unlinks head and sibling headers before readmission`() {
        fun flow(tail: Tail)=m.flowTree(AccessPathBase.Return,Layer.DEMAND,ExclusionSet.Empty,MarkSet.EMPTY,
            FlowAlgebra.prepend(m,m.path(listOf(f)),FlowAlgebra.LEAF_NODE),tail)
        for(starFirst in listOf(false,true)) {
            val store=DiagonalRelations(m)
            val star=facts(Tail.STAR,mark=u)
            val any=facts(Tail.ANY)
            if(starFirst) {store.add(initial(u),star);store.add(initial(),any)}
            else {store.add(initial(),any);store.add(initial(u),star)}
            store.compact(shape,flow(Tail.ANY))
            assertEquals(1,store.census().concreteOutputMemberships)
            assertNotNull(store.add(initial(),facts(Tail.STAR)))
            store.compact(shape,flow(Tail.STAR))
            assertTrue(store.isEmpty)
            assertNotNull(store.addDiagonal(packet(any)))
            assertEquals(1,store.census().concreteOutputMemberships)
            assertNull(store.add(initial(),facts(Tail.STAR)))
        }
    }
    companion object {
        @JvmStatic fun main(args: Array<String>) {
            val names=listOf(
                "stored ANY suppresses later STAR with ordinary and protected admission gates",
                "STAR before ANY stays nonminimal and repeated offers terminate",
                "ANY prefix covers STAR descendants and preserves late protected obligations",
                "partial cross-header flags and ordinary geometry use independent subtraction",
                "STAR exclusions cover and merge exactly as scalar admission in both orders",
                "mixed mark packet fallback is atomic and preserves its uncovered mark",
                "different initial base layer and output scope do not acquire cross-coverage",
                "summary owner uses the same cross-header admission without changing FLOW tail gates",
                "rewriting one atom preserves other shared geometry exclusions and protection",
                "FLOW compaction unlinks head and sibling headers before readmission",
            )
            var failed=0
            for(name in names)try {
                DiagonalTypedAdmissionTest::class.java.getDeclaredMethod(name).invoke(DiagonalTypedAdmissionTest())
                println("PASS $name")
            }catch(e: java.lang.reflect.InvocationTargetException){failed++;println("FAIL $name: ${e.targetException}")}
            check(failed==0){"$failed controls failed"}
        }
    }
}
