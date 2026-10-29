package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.*
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.*

class StaticOwnerEligibilityTest {
    /** Counts completed owner-set questions without production instrumentation. */
    private class Method(override val name: String, private val hash: Int) : CommonMethod {
        var hashCalls = 0
        var onHash: (() -> Unit)? = null
        override val parameters: List<CommonMethodParameter> = emptyList()
        override val returnType = object : CommonTypeName { override val typeName = "Object" }
        override fun flowGraph(): ControlFlowGraph<CommonInst> = error("unused")
        override fun hashCode(): Int { hashCalls++; onHash?.invoke(); return hash }
    }

    private fun counted(build: () -> FrozenStaticCompletion): FrozenStaticCompletion {
        val property = "org.opentaint.bidi.optimizationStatistics"
        val previous = System.getProperty(property)
        return try {
            System.setProperty(property, "true")
            build()
        } finally {
            if (previous == null) System.clearProperty(property) else System.setProperty(property, previous)
        }
    }

    @Test fun `visible view reuses true and false families across interleaved APIs and isolates new views`() {
        val f = EngineShellFixtures()
        val root = Method("root", 1)
        val yes = Method("reachable", 2)
        val no = Method("unreachable", 3)
        val outsideYes = Method("outsideYes", 4)
        val outsideNo = Method("outsideNo", 5)
        val calls: Map<CommonMethod, Set<CommonMethod>> = linkedMapOf(root to setOf(yes), no to emptySet())
        val graph = DetachedStaticCallGraph.copyOf(calls, f.cancellation)
        val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
        val fields = (0..2).map { f.field("s$it") }
        fun c(i: Int) = Pattern(PathFact(STATIC, listOf(cls, fields[i]), Tail.STAR, MarkSlot.STAR), ExclusionSet.Empty)
        val snapshot = counted { FrozenStaticCompletion.Builder(f.manager, graph).apply {
            addSeed(f.key(yes), c(0), c(1))
            addSeed(f.key(outsideYes), c(0), c(1))
            addSeed(f.key(no), c(0), c(2))
            addSeed(f.key(outsideNo), c(0), c(2))
        }.build() }
        val method = f.key(root)
        val view = snapshot.visible(method)
        var referenceEvaluations = 0
        fun reference(owners: Set<CommonMethod>): Boolean {
            referenceEvaluations++
            val pending = ArrayDeque<CommonMethod>().apply { add(root) }
            val seen = hashSetOf<CommonMethod>()
            while (pending.isNotEmpty()) {
                val next = pending.removeFirst()
                if (!seen.add(next)) continue
                if (next in owners) return true
                pending.addAll(calls[next].orEmpty())
            }
            return false
        }
        val expected = listOf(reference(setOf(yes, outsideYes)), reference(setOf(no, outsideNo)),
            reference(setOf(yes, outsideYes)), reference(setOf(no, outsideNo)))
        root.hashCalls = 0
        val actual = listOf(view.targets(c(1)).any(), view.targets(c(2)).any(),
            view.incoming(c(1)).any(), view.incoming(c(2)).any())
        assertEquals(expected, actual)
        assertEquals(4, referenceEvaluations, "The unoptimized owner test repeats all four questions")
        assertEquals(3, root.hashCalls, "Two owner-set tests plus one lazy graph-root lookup; repeated true and false add no tests")
        assertTrue("ownerFamilies=4" in snapshot.statistics())
        assertTrue("ownerEvaluations=2 ownerHits=2 ownerMemoViews=1 ownerMemoAllocatedBytes=4" in snapshot.statistics())

        val otherView = snapshot.visible(method)
        root.hashCalls = 0
        assertEquals(1, otherView.targets(c(1)).count())
        assertEquals(2, root.hashCalls, "A new query must compute its own owner answer and graph root")
        assertTrue("ownerEvaluations=3 ownerHits=2 ownerMemoViews=2 ownerMemoAllocatedBytes=8" in snapshot.statistics())
        f.cancellation.cancel()
        assertFailsWith<Cancellation.Cancelled> { view.incoming(c(1)).toList() }
    }

    @Test fun `C5 rejects packed rows before any owner question but C2 keeps them`() {
        val f = EngineShellFixtures()
        val root = Method("root", 1)
        val owner = Method("owner", 2)
        val outside = Method("outside", 3)
        val graph = DetachedStaticCallGraph.copyOf(mapOf(root to setOf(owner)), f.cancellation)
        val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
        fun c(name: String, mark: String) = Pattern(PathFact(STATIC,
            listOf(cls, f.field(name)), Tail.STAR, MarkSlot.Concrete(f.manager.marks.mark(mark))), ExclusionSet.Empty)
        val snapshot = FrozenStaticCompletion.Builder(f.manager, graph).apply {
            for (mark in listOf("T", "U", "V")) {
                addSeed(f.key(owner), c("a", mark), c("b", mark))
                addSeed(f.key(outside), c("a", mark), c("b", mark))
            }
        }.build()
        val view = snapshot.visible(f.key(root))
        root.hashCalls = 0
        val reject = StaticCandidateFilter { _, _, _ -> false }
        assertTrue(view.filteredTargets(c("b", "T"), true, reject).none())
        assertEquals(0, root.hashCalls, "Rejected packed labels must not touch their owner sets")
        assertEquals(3, view.targets(c("b", "T")).count(), "Unfiltered C2 enumeration is unchanged")
        assertEquals(4, root.hashCalls, "Three owner tests plus one graph-root lookup")
    }

    @Test fun `cancelled owner search installs no negative result`() {
        val f = EngineShellFixtures()
        val root = Method("root", 1)
        val owner = Method("owner", 2)
        val outside = Method("outside", 3)
        val graph = DetachedStaticCallGraph.copyOf(mapOf(root to setOf(owner)), f.cancellation)
        val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
        fun c(name: String) = Pattern(PathFact(STATIC,
            listOf(cls, f.field(name)), Tail.STAR, MarkSlot.STAR), ExclusionSet.Empty)
        val snapshot = FrozenStaticCompletion.Builder(f.manager, graph).apply {
            addSeed(f.key(owner), c("a"), c("b"))
            addSeed(f.key(outside), c("a"), c("b"))
        }.build()
        val view = snapshot.visible(f.key(root))
        root.onHash = { f.cancellation.cancel() }
        assertFailsWith<Cancellation.Cancelled> { view.targets(c("b")).toList() }
        root.onHash = null
        f.cancellation.activate()
        assertEquals(1, view.targets(c("b")).count(), "Retry must still perform and complete the graph search")
    }
}
