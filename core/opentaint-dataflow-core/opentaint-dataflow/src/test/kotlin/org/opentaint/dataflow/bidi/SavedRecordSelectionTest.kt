package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class SavedRecordSelectionTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val ops = f.ops
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.LocalVar(0)
    private val a = f.field("a")
    private val b = f.field("b")
    private val c = f.field("c")
    private val t = MarkSlot.Concrete(f.mark("T"))
    private val u = MarkSlot.Concrete(f.mark("U"))
    private val entry = BlockScope(BlockId(2), PortId(3))
    private val exit = PortId(4)
    private val reverseScope = BlockScope(entry.block, exit)

    private fun oracle(store: RecordStore, actual: Facts, direction: Direction): List<Record> {
        val seen = LinkedHashSet<Record>()
        for (leaf in ops.leaves(actual)) {
            for (record in store.byEntry(f.method, reverseScope, leaf)) if (record.direction == direction) seen += record
            for (record in store.byExit(f.method, reverseScope, leaf)) if (record.direction != direction) seen += record
        }
        return seen.toList()
    }

    private fun reversed(record: Record, actual: Facts): List<Pair<RecordLeafView, Boolean>> = buildList {
        val seen = LinkedHashSet<Pair<RecordLeafView, Boolean>>()
        for (leaf in ops.leaves(actual)) record.forEachReversedAt(leaf) { view, protected ->
            if (seen.add(view to protected)) add(view to protected)
        }
    }

    @Test fun `position selection equals native record discovery and leaf mark protection order`() {
        val store = PersistentRecordStore(ap)
        val protected = f.fact(y, listOf(a), mark=t) as TaintTree
        val initial = ap.initial(f.pattern(x,mark=t))
        val first = Record(f.method, Direction.FORWARD, initial, protected.withProtection(protected.root), entry, exit)
        val plain = Record(f.method, Direction.FORWARD, initial, f.fact(y, listOf(a,b), mark=u), entry, exit)
        val second = Record(f.method, Direction.BACKWARD, ap.initial(f.pattern(y,listOf(a),mark=t)),
            f.fact(x,mark=u), reverseScope, entry.entry)
        val third = Record(f.method, Direction.FORWARD, ap.initial(f.pattern(x,mark=u)),
            f.fact(y,listOf(c),mark=t), entry, exit)
        listOf(first,plain,second,third).forEach(store::add)
        val actual = ap.mergeAddDelta(f.fact(y,listOf(a),Tail.ANY,t),
            f.fact(y,listOf(c),Tail.ANY,t)).first
        val stats = SavedRecordSelectionStatistics()
        val selected = selectSavedRecords(store.view(), f.method, reverseScope, actual, ops, Direction.BACKWARD, stats)
        assertEquals(oracle(store,actual,Direction.BACKWARD),selected.map { it.record })
        for (selection in selected.filter { it.record.direction == Direction.FORWARD }) {
            val views = buildList { selection.forEachReversedAt(actual,ops) { view,protected -> add(view to protected) } }
            assertEquals(reversed(selection.record,actual),views)
        }
        assertEquals(1L,stats.queries)
        assertEquals(0L,stats.fallbackQueries)
        assertTrue(stats.reversedViews > 0)
        // Query metadata cannot change the observer's native record/exit identity.
        assertEquals(LoopObservedRecord(first,exit),LoopObservedRecord(first,exit,selected.first { it.record === first }))
    }

    @Test fun `unknown position capability falls back as a complete reader without changing order`() {
        val store=PersistentRecordStore(ap)
        val record=Record(f.method,Direction.FORWARD,ap.initial(f.pattern(x,mark=t)),
            ap.mergeAddDelta(f.fact(y,listOf(a),mark=t),f.fact(y,listOf(a,b),mark=u)).first,entry,exit)
        store.add(record)
        val unsupported=object:RecordStore by store.view() {
            override fun byExitPositions(method:MethodKey,scope:BlockScope,fact:Pattern):List<RecordOutputPosition>?=null
        }
        val actual=f.fact(y,listOf(a),Tail.ANY,t)
        val stats=SavedRecordSelectionStatistics()
        val selected=selectSavedRecords(unsupported,f.method,reverseScope,actual,ops,Direction.BACKWARD,stats)
        assertEquals(oracle(unsupported,actual,Direction.BACKWARD),selected.map { it.record })
        val views=buildList { selected.single().forEachReversedAt(actual,ops) { view,protected -> add(view to protected) } }
        assertEquals(reversed(record,actual),views)
        assertEquals(1L,stats.fallbackQueries)
    }

    @Test fun `positional reverse selection preserves native FLOW exclusions and MUST views`() {
        val store=PersistentRecordStore(ap)
        val flow=MarkSlot.Star(ap.markSetOf(u.mark))
        val excluded=ExclusionSet.Concrete(intArrayOf(c))
        // Native initials never carry mark exclusions; the saved output keeps its actual mx.
        val input=ap.initial(f.pattern(x,tail=Tail.ANY_TAINT,mark=MarkSlot.STAR,exclusion=excluded))
        val record=Record(f.method,Direction.FORWARD,input,
            ap.mergeAddDelta(f.fact(y,listOf(a),Tail.ANY_TAINT,flow,excluded),
                f.fact(y,listOf(b),Tail.ANY_TAINT,flow,excluded)).first,entry,exit)
        store.add(record)
        val actual=f.fact(y,listOf(a,c),Tail.ANY,t)
        val selected=selectSavedRecords(store,f.method,reverseScope,actual,ops,Direction.BACKWARD)
        val views=buildList { selected.single().forEachReversedAt(actual,ops) { view,protected -> add(view to protected) } }
        assertEquals(reversed(record,actual),views)
        assertTrue(views.isNotEmpty())
        assertTrue(views.all { it.first.premise.exclusion == excluded })
    }
}
