package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import kotlin.test.*

class RestrictedInitialPolicyTest {
    private val f = EngineShellFixtures()
    private val ap = f.manager
    private val a = f.field("a")
    private val b = f.field("b")
    private val t = MarkSlot.Concrete(ap.marks.mark("T"))
    private val u = MarkSlot.Concrete(ap.marks.mark("U"))
    private fun p(tail: Tail, mark: MarkSlot = MarkSlot.STAR, path: List<Int> = emptyList(),
                  e: ExclusionSet = ExclusionSet.Empty, base: AccessPathBase = AccessPathBase.Argument(0)) =
        Pattern(PathFact(base, path, tail, mark), e)
    private fun policy(run: Int = 2, limit: Int = 3) = RestrictedInitialPolicy(run, limit,
        if (run % 2 == 0) Direction.BACKWARD else Direction.FORWARD, ap.marks)

    @Test fun `ANY resolves one field and keeps the concrete exact one-field exception`() {
        val q = policy()
        assertEquals(p(Tail.STAR, path = listOf(a)), q.emit(p(Tail.ANY), p(Tail.EXACT, t, listOf(a,b))))
        assertEquals(p(Tail.STAR, t, listOf(a)), q.emit(p(Tail.ANY, t), p(Tail.EXACT, t, listOf(a,b))))
        assertEquals(p(Tail.EXACT, t, listOf(a)), q.emit(p(Tail.ANY, t), p(Tail.EXACT, t, listOf(a))))
        assertNull(q.emit(p(Tail.ANY, u), p(Tail.EXACT, t, listOf(a))))
        assertNull(q.emit(p(Tail.ANY, t), p(Tail.STAR, t)))
        assertEquals(p(Tail.EXACT), q.emit(p(Tail.ANY), p(Tail.EXACT, t)))
    }

    @Test fun `requested STAR has a descendant witness and need not emit itself`() {
        val q = policy(limit = 1)
        val d = p(Tail.STAR)
        assertEquals(d, q.emit(d, p(Tail.EXACT, t, listOf(a))))
        assertEquals(p(Tail.EXACT), q.emit(d, d))
        assertTrue(q.canEmitInitial(d, d))
        val capped = p(Tail.STAR, path = listOf(a))
        assertFalse(q.canEmitInitial(capped, capped))
        assertTrue(q.canStoreInitial(capped, capped), "Canonical STAR still has an exact raw preimage at the cap")
        assertNull(policy(run=3).emit(p(Tail.STAR,t), p(Tail.EXACT,t,listOf(a))))
    }

    @Test fun `demand field E and actual field E belong to their own prefix`() {
        val q = policy()
        assertNull(q.emit(p(Tail.ANY,t,listOf(a)), p(Tail.ANY_TAINT,t,e=ExclusionSet.of(a))))
        assertNull(q.emit(p(Tail.STAR,t,e=ExclusionSet.of(a)), p(Tail.EXACT,t,listOf(a))))
        assertEquals(p(Tail.STAR), q.emit(p(Tail.STAR,e=ExclusionSet.of(a)), p(Tail.EXACT,t,listOf(a))))
        assertEquals(p(Tail.STAR,t), q.emit(p(Tail.STAR,t), p(Tail.STAR,t,listOf(a),ExclusionSet.of(b))))
        assertEquals(p(Tail.ANY, path=listOf(a)), q.emit(p(Tail.ANY,path=listOf(a)),p(Tail.ANY,t)))
    }

    @Test fun `uniform starts require a forward run and preserve their own exclusion`() {
        val actual = p(Tail.ANY_TAINT,t,e=ExclusionSet.of(a))
        assertNull(policy().emit(p(Tail.ANY),actual))
        assertEquals(p(Tail.ANY_TAINT,e=ExclusionSet.of(a)),policy(3).emit(p(Tail.ANY),actual))
    }

    @Test fun `a group guide binds a supplied full mark and cannot create a group initial`() {
        val group = MarkSlot.Concrete(ap.marks.group(ap.marks.groupOf(t.mark)))
        val d=p(Tail.ANY,group)
        assertEquals(p(Tail.EXACT,t),policy().emit(d,p(Tail.EXACT,t)))
        assertTrue(policy().canEmitInitial(d,p(Tail.EXACT,t)))
        assertFalse(policy().canEmitInitial(d,p(Tail.EXACT,group)))
        assertNull(policy().emit(d,p(Tail.EXACT,u)))
    }

    @Test fun `static anchors stay indivisible and exact class markers stay exact`() {
        val cls = ap.accessors.index(ClassStaticAccessor("C"))
        val q=policy(limit=1)
        val d=p(Tail.ANY,base=STATIC)
        assertEquals(p(Tail.STAR,path=listOf(cls,a),base=STATIC),q.emit(d,p(Tail.EXACT,t,listOf(cls,a),base=STATIC)))
        assertNull(q.emit(d,p(Tail.EXACT,t,listOf(cls),base=STATIC)))
        val marker=p(Tail.EXACT,t,listOf(cls),base=STATIC)
        assertEquals(marker,q.emit(marker,marker))
    }

    @Test fun `finite scalar image agrees with executable witnesses at the current budget`() {
        val paths=listOf(emptyList(),listOf(a),listOf(b),listOf(a,a),listOf(a,b),listOf(b,a),listOf(b,b))
        for (run in listOf(2,3)) {
            val q=policy(run,limit=2)
            val demands=paths.flatMap { path -> listOf(Tail.ANY,Tail.STAR,Tail.EXACT).flatMap { tail ->
                listOf(MarkSlot.STAR,t).map { p(tail,it,path) }
            } }
            val inputs=paths.flatMap { path -> Tail.entries.flatMap { tail -> listOf(MarkSlot.STAR,t,u).map { p(tail,it,path) } } }
            for (d in demands) {
                val emitted=inputs.mapNotNull { q.emit(d,it) }.toSet()
                for (candidate in inputs) assertEquals(candidate in emitted,q.canEmitInitial(d,candidate),
                    "run=$run demand=$d candidate=$candidate")
            }
        }
    }
}
