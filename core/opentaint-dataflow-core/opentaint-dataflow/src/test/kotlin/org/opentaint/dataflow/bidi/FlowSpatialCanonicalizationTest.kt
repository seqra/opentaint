package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.test.*

class FlowSpatialCanonicalizationTest {
    private val fixture = StoreFixtures()
    private val v = StoreValues(fixture)
    private val m = fixture.manager

    @Test fun `a packet and both arrival orders retain only the broad MUST region`(): Unit = with(v) {
        val parent = leaf(p(),Tail.ANY_TAINT,MarkSlot.STAR,e=ex(h))
        val child = leaf(p(f,g),Tail.ANY_TAINT,MarkSlot.STAR,e=ex(h))
        for (packets in listOf(listOf(pack(parent,child)), listOf(pack(parent),pack(child)),listOf(pack(child),pack(parent)))) {
            val group = ConclusionGroup(m,m.newInterners())
            packets.forEach { group.addAll(it) }
            assertEquals(setOf(parent),group.all().flatMap { decoded(it).asSequence() }.toSet())
        }
    }

    @Test fun `only an immediate complete MUST child fills a parent hole`(): Unit = with(v) {
        val parent = leaf(p(),Tail.ANY_TAINT,MarkSlot.STAR,e=ex(f))
        val complete = leaf(p(f),Tail.ANY_TAINT,MarkSlot.STAR)
        for (child in listOf(complete,leaf(p(f),Tail.ANY_TAINT,MarkSlot.STAR,e=ex(h)),
                             leaf(p(f,g),Tail.ANY_TAINT,MarkSlot.STAR))) {
            for (parentFirst in listOf(false,true)) {
                val group = ConclusionGroup(m,m.newInterners())
                (if (parentFirst) listOf(parent,child) else listOf(child,parent)).forEach { group.addAll(pack(it)) }
                val expected = if (child == complete) setOf(parent.copy(exclusion=ExclusionSet.Empty)) else setOf(parent,child)
                assertEquals(expected,group.all().flatMap { decoded(it).asSequence() }.toSet())
            }
        }
    }

    @Test fun `MAY canonicalization removes a descendant in one packet`(): Unit = with(v) {
        val parent = leaf(p(),Tail.ANY,MarkSlot.STAR,Layer.DEMAND)
        val child = leaf(p(f,g),Tail.ANY,MarkSlot.STAR,Layer.DEMAND)
        val group = ConclusionGroup(m,m.newInterners())
        group.addAll(pack(parent,child))
        assertEquals(setOf(parent),group.all().flatMap { decoded(it).asSequence() }.toSet())
    }
}
