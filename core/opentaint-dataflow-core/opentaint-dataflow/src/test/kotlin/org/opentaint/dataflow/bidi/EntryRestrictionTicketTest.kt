package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.test.*

class EntryRestrictionTicketTest {
    @Test fun `checked ticket matches native restriction with protection and multiple output marks`() {
        run {
            val f = StoreFixtures()
            val x = AccessPathBase.Argument(0); val ret = AccessPathBase.Return
            val t = MarkSlot.Concrete(f.mark("T")); val path = f.field("f")
            val initial = f.manager.initial(f.pattern(x, mark = t))
            val policy = RestrictedInitialPolicy(3, 3, Direction.FORWARD, f.manager.marks)
            val pair = DemandPattern(f.pattern(x, mark = t), f.pattern(ret, listOf(path), Tail.ANY, t))
            val raw = f.fact(ret, listOf(path), Tail.ANY, t) as TaintTree
            val protected = raw.withProtection(raw.root)
            val ticket = assertNotNull(EntryRestrictionTicket.prepare(f.ops, initial.toPattern(), pair, policy))
            for (value in listOf(raw, protected, protected.withLayer(Layer.DEMAND))) {
                val expected = f.ops.restrict(initial, value, pair, policy)
                val actual = ticket.restrict(value)
                assertEquals(expected, actual)
                assertEquals(expected.map { (it as? TaintTree)?.nonSubsumable }, actual.map { (it as? TaintTree)?.nonSubsumable })
            }
        }
    }
}
