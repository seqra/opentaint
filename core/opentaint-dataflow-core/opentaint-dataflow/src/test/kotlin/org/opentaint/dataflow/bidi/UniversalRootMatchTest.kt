package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import kotlin.test.*

/** Prepared source-adapter control. Do not run during the project benchmark. */
class UniversalRootMatchTest {
    private fun universal(a: Facts, j: Pattern, mode: ApMode): Boolean =
        a.base == j.fact.base && j.fact.base != STATIC && j.fact.base != AccessPathBase.Zero &&
            j.fact.base !is AccessPathBase.CleanerTemporary &&
            j.fact.path.isEmpty() && j.fact.tail == Tail.STAR &&
            j.exclusion == ExclusionSet.Empty && j.fact.mark == MarkSlot.STAR &&
            (a is FlowTree || mode.markMode == MarkMode.FULL)

    private fun proposed(ops: ApOps, a: Facts, j: Pattern, mode: ApMode, record: Boolean): Facts? =
        if (universal(a, j, mode)) a else ops.satisfying(a, j, mode, record)

    @Test
    fun `universal FULL nonstatic premise retains each canonical actual header and protection`() {
        MethodAnalysisFixtures().use { f ->
            val p = AccessPathBase.Argument(0)
            val t = f.mark("T")
            val j = f.pattern(p, tail = Tail.STAR, mark = MarkSlot.STAR)
            val shapes = ArrayList<Facts>()
            for (tail in Tail.entries) for (layer in Layer.entries)
                for (path in listOf(emptyList(), listOf(f.field("f"))))
                    for (mark in listOf(MarkSlot.STAR, MarkSlot.Star(f.manager.markSetOf(t)), MarkSlot.Concrete(t)))
                        for (excluded in listOf(false, true)) {
                            if (excluded && tail !in listOf(Tail.STAR, Tail.ANY_TAINT) && mark !is MarkSlot.Star) continue
                            if (excluded && tail == Tail.ANY) continue
                            val e = if (excluded) ExclusionSet.of(f.field("blocked")) else ExclusionSet.Empty
                            val actual = f.fact(p, path, tail, mark, e, layer)
                            shapes += actual
                            if (actual is TaintTree) shapes += actual.withProtection(actual.root)
                        }
            val modes = listOf(
                ApMode(true, Direction.FORWARD, 1),
                ApMode(false, Direction.FORWARD, 2),
                ApMode(false, Direction.BACKWARD, 3),
            )
            var checked = 0
            for (actual in shapes) for (mode in modes) for (record in listOf(false, true)) {
                val legacy = assertNotNull(f.ops.satisfying(actual, j, mode, record))
                assertEquals(actual, legacy, "$mode $record ${f.ops.leaves(actual).toList()}")
                if (actual is TaintTree) assertEquals(actual.nonSubsumable, (legacy as TaintTree).nonSubsumable)
                assertSame(actual, proposed(f.ops, actual, j, mode, record))
                checked++
            }
            assertTrue(checked > 100)
        }
    }

    @Test
    fun `GROUP taint may change layer and marks so the generic prototype retains its fallback`() {
        MethodAnalysisFixtures().use { f ->
            val p = AccessPathBase.Argument(0)
            val actual = f.fact(p, tail = Tail.EXACT, mark = MarkSlot.Concrete(f.mark("T")))
            val j = f.pattern(p, tail = Tail.STAR, mark = MarkSlot.STAR)
            val mode = ApMode(true, Direction.FORWARD, 1, MarkMode.GROUP)
            val legacy = assertNotNull(f.ops.satisfying(actual, j, mode))
            assertEquals(Layer.DEMAND, legacy.layer)
            assertNotEquals(actual, legacy)
            assertFalse(universal(actual, j, mode))
            assertEquals(legacy, proposed(f.ops, actual, j, mode, false))
        }
    }

    @Test
    fun `excluded fields concrete marks nonroot paths exact and must premises cannot use the shortcut`() {
        MethodAnalysisFixtures().use { f ->
            val p = AccessPathBase.Argument(0)
            val mark = MarkSlot.Concrete(f.mark("T"))
            val actual = f.fact(p, path = listOf(f.field("f")), mark = mark)
            val mode = ApMode(false, Direction.FORWARD, 2)
            val queries = listOf(
                f.pattern(p, tail = Tail.STAR, mark = MarkSlot.STAR, exclusion = ExclusionSet.of(f.field("f"))),
                f.pattern(p, tail = Tail.STAR, mark = mark),
                f.pattern(p, path = listOf(f.field("g")), tail = Tail.STAR, mark = MarkSlot.STAR),
                f.pattern(p, tail = Tail.EXACT, mark = MarkSlot.STAR),
                f.pattern(p, tail = Tail.ANY_TAINT, mark = MarkSlot.STAR),
                f.pattern(AccessPathBase.Argument(1), tail = Tail.STAR, mark = MarkSlot.STAR),
            )
            for (query in queries) {
                assertFalse(universal(actual, query, mode))
                assertEquals(f.ops.satisfying(actual, query, mode), proposed(f.ops, actual, query, mode, false))
            }
        }
    }
}
