package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class RecordOutputPositionTest {
    private val f=StoreFixtures()
    private val ap=f.manager
    private val ops=f.ops
    private val x=AccessPathBase.Argument(0)
    private val y=AccessPathBase.LocalVar(0)
    private val a=f.field("a")
    private val b=f.field("b")
    private val c=f.field("c")
    private val t=MarkSlot.Concrete(f.mark("T"))
    private val u=MarkSlot.Concrete(f.mark("U"))
    private val scope=BlockScope(BlockId(2),PortId(3))
    private val exit=PortId(4)

    @Test fun `selected native output positions preserve reversed view order and protection`() {
        val store=PersistentRecordStore(ap)
        val first=f.fact(y,listOf(a),mark=t) as TaintTree
        val plain=ap.mergeAddDelta(f.fact(y,listOf(a,b),mark=u),f.fact(y,listOf(c),mark=t)).first
        val initial=ap.initial(f.pattern(x,mark=t))
        val records=listOf(
            Record(f.method,Direction.FORWARD,initial,first.withProtection(first.root),scope,exit),
            Record(f.method,Direction.FORWARD,initial,plain,scope,exit))
        records.forEach(store::add)
        val reverseScope=BlockScope(scope.block,exit)
        for (path in listOf(emptyList(),listOf(a),listOf(a,b),listOf(c),listOf(b))) {
            val actual=f.pattern(y,path,Tail.ANY,t)
            val selected=assertNotNull(store.byExitPositions(f.method,reverseScope,actual))
            assertTrue(selected.all { position -> records.any { it === position.record } })
            val expected=ArrayList<Pair<RecordLeafView,Boolean>>()
            for (record in records) record.forEachReversedAt(actual) { view,protected -> expected+=view to protected }
            val actualViews=ArrayList<Pair<RecordLeafView,Boolean>>()
            for (position in selected.sortedBy { it.ordinal })
                position.forEachReversedAt(actual) { view,protected -> actualViews+=view to protected }
            assertEquals(expected,actualViews,"query=$actual")
            if(path==listOf(a)) assertEquals(listOf(listOf(a),listOf(a,b)),selected.sortedBy { it.ordinal }.map { it.path })
        }
        assertTrue(assertNotNull(store.byExitPositions(f.method,scope,f.pattern(y))).isEmpty(),"Entry and exit interfaces cannot alias")
    }

    @Test fun `shared DAG suffix positions stay distinct and duplicate add is idempotent`() {
        val store=PersistentRecordStore(ap)
        val output=ap.mergeAddDelta(f.fact(y,listOf(a,c),mark=t),f.fact(y,listOf(b,c),mark=t)).first
        val record=Record(f.method,Direction.FORWARD,ap.initial(f.pattern(x,mark=t)),output,scope,exit)
        store.add(record);store.add(record)
        val positions=assertNotNull(store.byExitPositions(f.method,BlockScope(scope.block,exit),f.pattern(y)))
        assertEquals(2,positions.size)
        assertEquals(setOf(listOf(a,c),listOf(b,c)),positions.map { it.path }.toSet())
        val only=assertNotNull(store.byExitPositions(f.method,BlockScope(scope.block,exit),f.pattern(y,listOf(a))))
        assertEquals(listOf(listOf(a,c)),only.map { it.path })
        assertSame(record,only.single().record)
    }
}
