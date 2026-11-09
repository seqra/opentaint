package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Native authority tests: an intermediate specialization is never inserted. */
class AlignedRelationCoverageTest {
    private val fixture = StoreFixtures()
    private val v = StoreValues(fixture)
    private val m = fixture.manager

    @Test fun `short NORMAL FLOW covers long FLOW and plain T regardless arrival order`(): Unit = with(v) {
        val a = premise(tail=Tail.STAR,mark=MarkSlot.STAR)
        val b = premise(p(f),Tail.STAR,MarkSlot.STAR)
        val c = premise(p(f),Tail.STAR,mt)
        val short = pack(leaf(p(),Tail.STAR,MarkSlot.STAR,base=y))
        val long = pack(leaf(p(f),Tail.STAR,MarkSlot.STAR,base=y))
        val marked = pack(leaf(p(f),Tail.STAR,mt,Layer.DEMAND,base=y))
        for (rows in listOf(listOf(a to short,b to long,c to marked),
                            listOf(c to marked,b to long,a to short),
                            listOf(c to marked,a to short))) {
            val store = RunSummaryStore(m,flowBacked=true)
            rows.forEach { (p,f) -> store.addAdmittedAll(p,f) }
            assertEquals(setOf(a to short),store.all().toSet())
            assertTrue(store.borrow(c).none())
            assertTrue(store.demandEdges(Direction.FORWARD).none())
        }
    }

    @Test fun `both exclusions and correlated shift control relation coverage`(): Unit = with(v) {
        val a = premise(tail=Tail.STAR,mark=MarkSlot.STAR,e=ex(g))
        val b = premise(p(f),Tail.STAR,MarkSlot.STAR)
        val wrongShift = premise(p(g),Tail.STAR,MarkSlot.STAR)
        val short = pack(leaf(p(),Tail.STAR,MarkSlot.STAR,e=ex(h),base=y))
        val covered = pack(leaf(p(f),Tail.STAR,MarkSlot.STAR,base=y))
        val mismatch = pack(leaf(p(h),Tail.STAR,MarkSlot.STAR,base=y))
        val store = RunSummaryStore(m,true)
        store.addAdmittedAll(a,short)
        assertTrue(store.addAdmittedAll(b,covered).isEmpty())
        assertTrue(store.addAdmittedAll(wrongShift,pack(leaf(p(g),Tail.STAR,MarkSlot.STAR,base=y))).isNotEmpty())
        assertTrue(store.addAdmittedAll(b,mismatch).isNotEmpty())
    }

    @Test fun `protected diagonal is retained while plain specialization is covered`(): Unit = with(v) {
        val a = premise(tail=Tail.STAR,mark=MarkSlot.STAR)
        val c = premise(p(f),Tail.STAR,mt)
        val marked = pack(leaf(p(f),Tail.STAR,mt,Layer.DEMAND,base=y)) as TaintTree
        val store = RunSummaryStore(m,true)
        store.addAdmittedAll(c,marked)
        store.addAdmittedAll(c,marked.withProtection(marked.root))
        store.addAdmittedAll(a,pack(leaf(p(),Tail.STAR,MarkSlot.STAR,base=y)))
        val kept = store.borrow(c).toList()
        assertEquals(1,kept.size)
        assertNotNull((kept.single() as TaintTree).nonSubsumable)
    }

    @Test fun `barrier rebuild removes historical long records from both read indexes`(): Unit = with(v) {
        val records = PersistentRecordStore(m)
        val a = premise(tail=Tail.STAR,mark=MarkSlot.STAR)
        val b = premise(p(f),Tail.STAR,MarkSlot.STAR)
        val short = pack(leaf(p(),Tail.STAR,MarkSlot.STAR,base=y))
        val long = pack(leaf(p(f),Tail.STAR,MarkSlot.STAR,base=y))
        val one = RunSummaryStore(m,true).also { it.addAdmittedAll(b,long) }
        records.persist(Direction.FORWARD,sequenceOf(fixture.method to one))
        val two = RunSummaryStore(m,true).also { it.addAdmittedAll(a,short) }
        records.persist(Direction.FORWARD,sequenceOf(fixture.method to two))
        val input = Pattern(PathFact(x,p(f),Tail.STAR,MarkSlot.STAR),ExclusionSet.Empty)
        val output = Pattern(PathFact(y,p(f),Tail.STAR,MarkSlot.STAR),ExclusionSet.Empty)
        assertEquals(listOf(a),records.byEntry(fixture.method,input).map { it.premise }.toList())
        assertEquals(listOf(a),records.byExit(fixture.method,output).map { it.premise }.toList())
    }

    @Test fun `ordinary STAR ancestor only matches an opposite saved record`(): Unit = with(v) {
        val actual = pack(leaf(p(),Tail.STAR,mt,Layer.DEMAND))
        val initial = premise(p(f),Tail.STAR,mt)
        val mode = ApMode(run1=false,direction=Direction.FORWARD,fieldLimit=3)
        assertNull(fixture.ops.satisfying(actual,initial,mode))
        assertNull(fixture.ops.satisfying(actual,initial,mode,record=true))
        assertNotNull(fixture.ops.satisfying(actual,initial,mode,record=true,role=SummaryReadRole.SAVED_OPPOSITE))
    }

    @Test fun `same-head MUST overlap applies a retained FLOW provider`(): Unit = with(v) {
        val actual = pack(leaf(p(),Tail.ANY_TAINT,mt,e=ex(g)))
        val initial = premise(tail=Tail.STAR,mark=MarkSlot.STAR,e=ex(f))
        val summary = pack(leaf(p(),Tail.STAR,MarkSlot.STAR,base=y))
        val mode = ApMode(run1=false,direction=Direction.FORWARD,fieldLimit=3)
        val matched = assertNotNull(fixture.ops.satisfying(actual,initial,mode))
        val out = CollectingOut()
        fixture.ops.applySummary(matched,initial,summary,mode,out)
        assertEquals(setOf(leaf(p(),Tail.ANY_TAINT,mt,e=ex(f,g),base=y)),out.results.flatMap { decoded(it) }.toSet())
    }
    @Test fun `removed FLOW and concrete premise indexes release keys and admit a later new row`(): Unit = with(v) {
        val removed = arrayListOf<PremiseKey>()
        val owner = FlowBackedSummaries(m, onPremiseRemoved = { removed += it })
        val shortKey = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        val longKey = premise(p(f), Tail.STAR, MarkSlot.STAR)
        val concrete = premise(p(f), Tail.STAR, mt)
        val short = pack(leaf(p(), Tail.STAR, MarkSlot.STAR, base = y))
        val long = pack(leaf(p(f), Tail.STAR, MarkSlot.STAR, base = y))
        val marked = pack(leaf(p(f), Tail.STAR, mt, Layer.DEMAND, base = y))
        owner.addAll(concrete, marked)
        owner.addAll(longKey, long)
        owner.addAll(shortKey, short)
        assertEquals(setOf(longKey, concrete), removed.toSet())
        assertTrue(owner.borrow(longKey).none())
        assertTrue(owner.borrow(concrete).none())
        val changed = pack(leaf(p(g), Tail.STAR, mt, Layer.DEMAND, base = y))
        assertTrue(owner.addAll(concrete, changed).isNotEmpty())
        // It must be indexed again: a newly added aligned provider removes it.
        val provider = pack(leaf(p(g), Tail.STAR, MarkSlot.STAR, base = y))
        owner.addAll(longKey, provider)
        assertTrue(owner.borrow(concrete).none())
        assertEquals(2, removed.count { it === concrete })
    }

}
