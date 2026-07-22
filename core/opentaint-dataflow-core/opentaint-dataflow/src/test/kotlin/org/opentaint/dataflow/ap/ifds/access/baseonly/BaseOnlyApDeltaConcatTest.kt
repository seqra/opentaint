package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class BaseOnlyApDeltaConcatTest {
    private val accessors = AccessorInterner()
    private val ai = BaseOnlyAccessOps

    private val field = FieldAccessor("A", "f", "B")
    private val field2 = FieldAccessor("A", "g", "B")
    private val mark = TaintMarkAccessor("m")
    private val stat = ClassStaticAccessor("T")
    private val final = FinalAccessor

    private fun i(a: org.opentaint.dataflow.ap.ifds.Accessor) = accessors.index(a)

    private fun chain(vararg a: org.opentaint.dataflow.ap.ifds.Accessor, abstract: Boolean = false): BaseOnlyAccess =
        ai.build(IntArray(a.size) { i(a[it]) }, abstract)

    @Test
    fun `concat closed fact rejects non-empty delta`() {
        val markFact = chain(mark)
        assertNull(ai.appendFinal(markFact, chain(mark)))
        assertEquals(markFact, ai.appendFinal(markFact, ai.empty))
    }

    @Test
    fun `concat suffix-AP widens a field-leading cross-kind delta`() {
        val f0Abstract = ai.abstractAt(NO_ACCESSOR, i(field), 2)
        val deltaFieldMark = chain(field2, mark)
        assertEquals(chain(field, mark), ai.appendFinal(f0Abstract, deltaFieldMark))
    }

    @Test
    fun `delta requires initial le final`() {
        val c = chain(mark)
        val iValue = chain(final)
        val m = ai.matchPrefix(c, iValue)
        assertFalse(m.emptyDelta)
        assertFalse(m.hasSuffix)
    }

    @Test
    fun `delta abstract initial yields whole final`() {
        val c = chain(mark)
        val m = ai.matchPrefix(c, ai.abstractEmpty)
        assertFalse(m.emptyDelta)
        assertTrue(m.hasSuffix)
        assertEquals(chain(mark), m.suffix)
    }

    @Test
    fun `splitConcreteInitial splits a closed value against a fully abstract final`() {
        val closedInitial = chain(mark)
        val abstractFinal = ai.abstractEmpty
        assertFalse(ai.matchPrefix(abstractFinal, closedInitial).emptyDelta)
        assertFalse(ai.matchPrefix(abstractFinal, closedInitial).hasSuffix)
        val split = ai.splitConcreteInitial(abstractFinal, closedInitial)!!
        assertEquals(abstractFinal, split.matched)
        assertEquals(chain(mark), split.delta)
    }

    @Test
    fun `splitConcreteInitial keeps the tail of a closed field initial past a field-abstract final`() {
        val closedInitial = chain(field, mark)
        val fieldAbstract = ai.abstractAt(NO_ACCESSOR, i(field), 2)
        val split = ai.splitConcreteInitial(fieldAbstract, closedInitial)!!
        assertEquals(fieldAbstract, split.matched)
        assertEquals(chain(mark), split.delta)
    }

    @Test
    fun `BaseOnly resolves the Stirling semantic sink branch after lossy normalization`() {
        val manager = BaseOnlyApManager(
            AnyAccessorUnrollStrategy.AnyAccessorDisabled,
            fieldSensitive = true,
        )
        val body = FieldAccessor("Response", "Body", "Token")
        val sink = TaintMarkAccessor("sink_35")
        val bodyIdx = manager.interner.index(body)
        val sinkIdx = manager.interner.index(sink)
        val summaryAccess = ai.build(intArrayOf(bodyIdx), isAbstract = true)
        val callerAccess = ai.build(intArrayOf(sinkIdx), isAbstract = false)
        val base = AccessPathBase.Argument(0)
        // BaseOnly normalized the Tree union `Body.* | sink_35.$` to
        // `Body.* / {sink_35}`, dropping the explicit semantic-mark branch.
        val summaryFinal = BaseOnlyFinalFactAp(
            manager,
            base,
            summaryAccess,
            ExclusionSet.Concrete(sink),
        )
        val callerFact = BaseOnlyInitialFactAp(
            manager,
            base,
            callerAccess,
            ExclusionSet.Empty,
        )
        val splits = callerFact.splitDelta(summaryFinal)

        assertEquals(1, splits.size, "the structural summary exclusion must not reject a semantic trace mark")
        assertEquals(summaryAccess, (splits.single().first as BaseOnlyInitialFactAp).access)
        assertEquals(
            callerAccess,
            (splits.single().second as BaseOnlyNodeInitialDelta).access,
            "the sink-only caller suffix must survive as the trace delta",
        )
    }

    @Test
    fun `Tree resolves the Stirling semantic sink branch retained beside the open body branch`() {
        val manager = TreeApManager(
            AnyAccessorUnrollStrategy.AnyAccessorDisabled,
            RefManager(),
        )
        val body = FieldAccessor("Response", "Body", "Token")
        val sink = TaintMarkAccessor("sink_35")
        val bodyIdx = manager.interner.index(body)
        val sinkIdx = manager.interner.index(sink)
        val base = AccessPathBase.Argument(0)

        // This is the Tree summary observed for the same call boundary: the open
        // response-body branch and the explicit semantic sink branch coexist.
        val bodyBranch = manager.abstractNode.addParent(bodyIdx)
        val sinkBranch = manager.finalNode.addParent(sinkIdx)
        val summaryFinal = AccessTree(
            manager,
            base,
            bodyBranch.mergeAdd(sinkBranch),
            ExclusionSet.Empty,
        )
        val callerAccess = AccessPath.AccessNode(
            manager,
            sinkIdx,
            AccessPath.AccessNode(manager, manager.interner.index(FinalAccessor), null),
        )
        val callerFact = AccessPath(manager, base, callerAccess, ExclusionSet.Empty)

        val (matched, delta) = callerFact.splitDelta(summaryFinal).single()
        assertEquals(callerFact, matched)
        assertTrue(delta.isEmpty)
    }

    @Test
    fun `splitConcreteInitial rejects abstract initial, concrete final, and prefix mismatch`() {
        assertNull(ai.splitConcreteInitial(ai.abstractEmpty, ai.abstractEmpty))
        assertNull(ai.splitConcreteInitial(chain(mark), chain(mark)))
        assertNull(ai.splitConcreteInitial(ai.abstractAt(NO_ACCESSOR, i(field), 2), chain(field2, mark)))
    }

    @Test
    fun `AP@base wildcard covers every fact`() {
        val apStatic = ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0)
        assertTrue(ai.containsAccess(apStatic, chain(stat, mark)))
        assertTrue(ai.containsAccess(apStatic, chain(mark)))
        assertTrue(ai.containsAccess(apStatic, chain(field, mark)))
    }

    @Test
    fun `AP@suffix empty covers static-less terminals including field-carrying`() {
        val apSuffixEmpty = ai.abstractEmpty
        assertTrue(ai.containsAccess(apSuffixEmpty, chain(mark)))
        assertFalse(ai.containsAccess(apSuffixEmpty, chain(stat, mark)))
        assertTrue(ai.containsAccess(apSuffixEmpty, chain(field, mark)))
    }

    @Test
    fun `AP@suffix containment is field-lenient after lossy projection`() {
        val apSuffixField = ai.abstractAt(NO_ACCESSOR, i(field), 2)
        assertTrue(ai.containsAccess(apSuffixField, chain(field, mark)))
        assertTrue(ai.containsAccess(apSuffixField, chain(mark)))
        assertFalse(ai.covers(apSuffixField, chain(mark)), "storage subsumption remains directional")
    }

    @Test
    fun `splitConcreteInitial known-empty field is field-lenient`() {
        val apSuffixEmpty = ai.abstractEmpty
        val fieldSplit = ai.splitConcreteInitial(apSuffixEmpty, chain(field, mark))!!
        assertEquals(apSuffixEmpty, fieldSplit.matched)
        assertEquals(chain(mark), fieldSplit.delta)
        val split = ai.splitConcreteInitial(apSuffixEmpty, chain(mark))!!
        assertEquals(chain(mark), split.delta)
    }

    @Test
    fun `trace append accepts a cross-kind terminal delta at an AP@static prefix`() {
        val apStaticPrefix = ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0)
        val result = ai.append(apStaticPrefix, chain(mark))
        assertNotNull(result)
        assertEquals(chain(mark), result)
    }
}
