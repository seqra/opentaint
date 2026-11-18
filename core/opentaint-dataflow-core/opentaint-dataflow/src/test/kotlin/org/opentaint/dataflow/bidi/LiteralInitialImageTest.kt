package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class LiteralInitialImageTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val t = fixture.mark("T")
    private val u = fixture.mark("U")
    private val f = fixture.field("f")
    private val g = fixture.field("g")

    /** Direct typed construction is independent of recognition and does not normalize initials. */
    private fun image(i: InitialAp, layer: Layer): Facts = when (val mark = i.mark) {
        is MarkSlot.Star -> m.flowTree(i.base, layer, i.exclusion, MarkExclusions.EMPTY,
            FlowAlgebra.prepend(m, i.path, FlowAlgebra.LEAF_NODE), i.tail)
        is MarkSlot.Concrete -> {
            val singleton = m.markSetOf(mark.mark)
            val leaf = if (i.tail == Tail.EXACT) m.taintLeaves(singleton, MarkSet.EMPTY)
                else m.taintLeaves(MarkSet.EMPTY, singleton)
            m.taintTree(i.base, layer, m.taintAlg.prepend(m, i.path, m.taintAlg.leafNode(leaf)),
                i.exclusion, if (i.tail == Tail.EXACT) Tail.ANY_TAINT else i.tail)
        }
    }

    @Test
    fun `all canonical typed images reconstruct without abstraction and keep their complete headers`() {
        val clazz = m.accessors.index(ClassStaticAccessor("Box"))
        val bases = listOf(AccessPathBase.Argument(0), AccessPathBase.This, AccessPathBase.Return,
            AccessPathBase.ClassStatic)
        for (base in bases) for (path in listOf(emptyList(), listOf(f), listOf(clazz), listOf(clazz, f, g))) {
            for (tail in Tail.entries) for (flow in listOf(false, true)) {
                val exclusions = if (tail == Tail.STAR || tail == Tail.ANY_TAINT)
                    listOf(ExclusionSet.Empty, ExclusionSet.of(g)) else listOf(ExclusionSet.Empty)
                for (e in exclusions) for (layer in Layer.entries) {
                    if (flow && tail == Tail.ANY && layer == Layer.NORMAL) continue
                    val i = m.initial(base, m.path(path), tail, e,
                        if (flow) MarkSlot.STAR else MarkSlot.Concrete(t))
                    val f = image(i, layer)
                    assertEquals(PLAIN_IDENTITY, m.identityKind(i, f))
                    val restored = initialImage(m, i, layer, false)
                    assertEquals(f, restored)
                    assertEquals((f as? TaintTree)?.nonSubsumable, (restored as? TaintTree)?.nonSubsumable)
                    if (!flow) {
                        f as TaintTree
                        val protected = f.withProtection(f.root)
                        assertEquals(PROTECTED_IDENTITY, m.identityKind(i, protected))
                        val p = initialImage(m, i, layer, true) as TaintTree
                        assertEquals(protected, p)
                        assertEquals(protected.nonSubsumable, p.nonSubsumable)
                    }
                }
            }
        }
    }

    @Test
    fun `recognition rejects extra leaves marks geometry headers and noncanonical masks`() {
        val i = m.initial(AccessPathBase.Argument(0), m.path(listOf(f)), Tail.STAR,
            ExclusionSet.of(g), MarkSlot.Concrete(t))
        val identity = image(i, Layer.NORMAL) as TaintTree
        val other = m.taintAlg.prepend(m, m.path(listOf(g)),
            m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, m.markSetOf(t))))
        val multi = m.taintAlg.mergeAdd(identity.root, other)
        val wrongMark = m.taintAlg.prepend(m, i.path,
            m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, m.markSetOf(u))))
        val extraMark = m.taintAlg.mergeAdd(identity.root, wrongMark)
        val parent = m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, m.markSetOf(t)))
        val child = m.taintAlg.prepend(m, m.path(listOf(f, g)), parent)
        val cases = listOf(
            m.taintTree(i.base, Layer.NORMAL, multi, i.exclusion, i.tail),
            m.taintTree(i.base, Layer.NORMAL, extraMark, i.exclusion, i.tail),
            m.taintTree(i.base, Layer.NORMAL, m.taintAlg.mergeAdd(identity.root, parent), i.exclusion, i.tail),
            m.taintTree(i.base, Layer.NORMAL, m.taintAlg.mergeAdd(identity.root, child), i.exclusion, i.tail),
            m.taintTree(i.base, Layer.NORMAL, identity.root, ExclusionSet.Empty, i.tail),
            m.taintTree(i.base, Layer.NORMAL, identity.root, i.exclusion, Tail.ANY_TAINT),
            m.taintTree(AccessPathBase.Return, Layer.NORMAL, identity.root, i.exclusion, i.tail),
            // Unsupported raw masks must never be discarded by recognition.
            TaintTree(i.base, Layer.NORMAL, identity.root, i.exclusion, i.tail, other),
        )
        for (f in cases) assertEquals(NOT_IDENTITY, m.identityKind(i, f))
        assertEquals(NOT_IDENTITY, m.identityKind(m.zero, Reach.NORMAL))
        val flow = m.initial(i.base, i.path, Tail.STAR, i.exclusion, MarkSlot.STAR)
        val flowIdentity = image(flow, Layer.NORMAL) as FlowTree
        assertEquals(NOT_IDENTITY, m.identityKind(flow,
            m.flowTree(flow.base, Layer.NORMAL, flow.exclusion, m.markSetOf(t), flowIdentity.root, flow.tail)))
        assertEquals(NOT_IDENTITY, m.identityKind(flow,
            m.flowTree(flow.base, Layer.NORMAL, flow.exclusion, MarkExclusions.EMPTY,
                FlowAlgebra.mergeAdd(flowIdentity.root, FlowAlgebra.LEAF_NODE), flow.tail)))
    }

    @Test
    fun `long image walk and reconstruction remain stack safe and cancellable`() {
        val i = m.initial(AccessPathBase.Argument(0), m.path(List(32768) { f }), Tail.EXACT,
            ExclusionSet.Empty, MarkSlot.Concrete(t))
        val original = image(i, Layer.DEMAND)
        assertEquals(PLAIN_IDENTITY, m.identityKind(i, original))
        assertEquals(original, initialImage(m, i, Layer.DEMAND, false))
        fixture.cancellation.cancel()
        try {
            assertFailsWith<Cancellation.Cancelled> { m.identityKind(i, original) }
        } finally { fixture.cancellation.activate() }
    }
}
