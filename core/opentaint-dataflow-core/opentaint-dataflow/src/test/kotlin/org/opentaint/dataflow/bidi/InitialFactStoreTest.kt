package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.InitialFactStore
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.test.*

class InitialFactStoreTest {
    @Test fun `exact canonical identity retains every tail mark and field exclusion`() {
        val fixture = StoreFixtures()
        val m = fixture.manager
        val f = fixture.field("f")
        val g = fixture.field("g")
        val t = fixture.mark("T")
        val u = fixture.mark("U")
        val store = InitialFactStore()
        val initials = mutableListOf(m.zero)
        for (path in listOf(emptyList(), listOf(f))) {
            for (tail in listOf(Tail.STAR, Tail.ANY)) initials += m.initial(fixture.pattern(path = path, tail = tail, mark = MarkSlot.STAR))
            initials += m.initial(fixture.pattern(path = path, tail = Tail.STAR, mark = MarkSlot.STAR, exclusion = ExclusionSet.of(g)))
            for (mark in listOf(t, u)) for (tail in Tail.entries) {
                initials += m.initial(fixture.pattern(path = path, tail = tail, mark = MarkSlot.Concrete(mark)))
                if (tail == Tail.STAR || tail == Tail.ANY_TAINT)
                    initials += m.initial(fixture.pattern(path = path, tail = tail, mark = MarkSlot.Concrete(mark), exclusion = ExclusionSet.of(g)))
            }
        }
        initials += initials.filterNot { it.isZero }.map {
            m.initial(it.toPattern().copy(fact = it.toPattern().fact.copy(base = org.opentaint.dataflow.ap.ifds.AccessPathBase.Return)))
        }
        assertEquals(initials.size, initials.toSet().size)
        assertTrue(store.all().isEmpty())
        for (i in initials) {
            assertTrue(store.add(i))
            assertFalse(store.add(i))
            assertFalse(store.add(m.initial(i.toPattern())))
        }
        assertEquals(initials.toSet(), store.all().toSet())
        for (i in initials) assertEquals(ApOps(m).startFact(i).layer, intrinsicInitialLayer(i))
    }

    @Test fun `same key starts each canonical layer once in either arrival order`() {
        val f = StoreFixtures()
        val i = f.manager.initial(f.pattern(mark = MarkSlot.Concrete(f.mark("T")), tail = Tail.EXACT))
        for (order in listOf(listOf(Layer.NORMAL, Layer.DEMAND), listOf(Layer.DEMAND, Layer.NORMAL))) {
            val store = InitialFactStore()
            for (layer in order) {
                assertTrue(store.add(AdmittedInitial(i, layer)))
                assertFalse(store.add(AdmittedInitial(i, layer)))
            }
            assertEquals(setOf(i), store.all().toSet())
            assertEquals(setOf(AdmittedInitial(i, Layer.NORMAL), AdmittedInitial(i, Layer.DEMAND)), store.admissions().toSet())
        }
    }

    @Test fun `intrinsic STAR and run1 GROUP floors have no fictitious NORMAL membership and ZERO stays NORMAL`() {
        val f = StoreFixtures()
        val m = f.manager
        val mark = MarkSlot.Concrete(f.mark("T"))
        val star = m.initial(f.pattern(mark = mark, tail = Tail.STAR))
        val store = InitialFactStore()
        assertTrue(store.add(AdmittedInitial(star, Layer.NORMAL)))
        assertFalse(store.add(AdmittedInitial(star, Layer.DEMAND)))
        assertEquals(listOf(AdmittedInitial(star, Layer.DEMAND)), store.admissions())
        val groupMode = ApMode(true, Direction.FORWARD, 1, MarkMode.GROUP)
        val exact = m.initial(f.pattern(mark = mark, tail = Tail.EXACT))
        assertEquals(AdmittedInitial(exact, Layer.DEMAND), canonicalAdmission(exact, Layer.NORMAL, groupMode))
        assertEquals(existingZeroAdmission(m.zero), canonicalAdmission(m.zero, Layer.NORMAL, groupMode))
        assertEquals(existingZeroAdmission(m.zero), canonicalAdmission(m.zero, Layer.NORMAL,
            ApMode(true, Direction.FORWARD, 1, MarkMode.FULL)))
    }
}
