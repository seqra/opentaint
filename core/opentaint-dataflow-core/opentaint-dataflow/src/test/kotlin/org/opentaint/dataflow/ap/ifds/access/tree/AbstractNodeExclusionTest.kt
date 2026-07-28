package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertIs
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

/**
 * The combination laws of the abstraction's excluded-mark annotation ([AbstractionExclusions]).
 *
 * A starred sanitizer cleans a fact structurally ([FinalFactAp.deepClean]): concrete `![m]` nodes
 * below the base are deleted outright, and each abstract node picks up the residual claim that the
 * mark stays excluded from whatever materializes below it later. The claim is PART OF THE NODE, so
 * it travels with a prepend, is confined to its branch, is enforced when a summary delta is
 * concatenated at the node, and joins by intersection when two alternatives meet at the same node.
 */
class AbstractNodeExclusionTest {

    private companion object {
        val FIELD_RAW = FieldAccessor("Pair", "raw", "Box")
        val FIELD_VAL = FieldAccessor("Pair", "val", "Box")
        val FIELD_F = FieldAccessor("Box", "f", "String")

        val MARK = TaintMarkAccessor("m")
        val MARK_2 = TaintMarkAccessor("n")
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())

    private val base = AccessPathBase.This

    private fun abstractFact(): AccessTree = manager.mostAbstractFinalAp(base) as AccessTree

    private fun concreteFact(vararg accessors: Accessor): AccessTree {
        var fact = manager.createFinalAp(base, org.opentaint.dataflow.ap.ifds.ExclusionSet.Empty)
        for (accessor in accessors.reversed()) {
            fact = fact.prependAccessor(accessor)
        }
        return fact as AccessTree
    }

    private fun FinalFactAp.deepCleaned(mark: TaintMarkAccessor = MARK): AccessTree {
        val result = deepClean(mark)
        assertIs<FinalFactAp.DeepCleanResult.Cleaned>(result, "expected a surviving fact")
        return result.fact as AccessTree
    }

    private fun merged(a: AccessTree, b: AccessTree): AccessTree =
        AccessTree(manager, base, a.access.mergeAdd(b.access), a.exclusions)

    /** The caller-side content that tries to materialize below the exit fact's abstract nodes. */
    private fun deltaOf(fact: AccessTree): FinalFactAp.Delta {
        val deltas = fact.delta(manager.mostAbstractInitialAp(base))
        return deltas.single { !it.isEmpty }
    }

    private fun FinalFactAp.readsMarkAt(vararg accessors: Accessor): Boolean {
        var node: FinalFactAp = this
        for (accessor in accessors) {
            node = node.readAccessor(accessor) ?: return false
        }
        return node.startsWithAccessor(MARK)
    }

    /* ---------- the clean itself ---------- */

    @Test
    fun `deep clean deletes concrete marks below the base and keeps the base mark`() {
        // this.![m], this.f.![m] — one is the base action's territory, one is the star's
        val fact = merged(concreteFact(MARK), concreteFact(FIELD_F, MARK))

        val cleaned = fact.deepCleaned()

        assertTrue(cleaned.startsWithAccessor(MARK), "the direct base mark is the base action's job")
        assertFalse(cleaned.readsMarkAt(FIELD_F), "the mark below a field must be deleted")
    }

    @Test
    fun `deep clean removes a fact that was only deep marks`() {
        val fact = concreteFact(FIELD_F, MARK)

        assertIs<FinalFactAp.DeepCleanResult.RemovedCompletely>(fact.deepClean(MARK))
    }

    @Test
    fun `deep clean leaves an unrelated mark alone`() {
        val fact = concreteFact(FIELD_F, MARK_2)

        val cleaned = fact.deepCleaned(MARK)

        assertTrue(
            cleaned.readAccessor(FIELD_F)?.startsWithAccessor(MARK_2) == true,
            "an unrelated mark below a field must survive"
        )
    }

    @Test
    fun `deep clean annotates an abstract fact instead of dropping it`() {
        val cleaned = abstractFact().deepCleaned()

        assertTrue(cleaned.isAbstract(), "the abstraction itself survives the clean")
        assertNotNull(cleaned.access.abstraction, "the abstract node must carry the claim")
    }

    /* ---------- enforcement at concat ---------- */

    @Test
    fun `a delta below the annotated base loses the mark under a field and keeps the direct mark`() {
        val exit = abstractFact().deepCleaned()
        val delta = deltaOf(merged(concreteFact(MARK), concreteFact(FIELD_F, MARK)))

        val applied = exit.concat(FactTypeChecker.Dummy, delta)

        assertNotNull(applied, "the direct base mark keeps the fact alive")
        assertTrue(applied.startsWithAccessor(MARK), "depth-1 mark is outside the star's claim")
        assertFalse(applied.readsMarkAt(FIELD_F), "depth-2 mark materializing below the base must be blocked")
    }

    @Test
    fun `a delta that is only excluded marks does not survive the concat`() {
        val exit = abstractFact().deepCleaned()
        val delta = deltaOf(concreteFact(FIELD_F, MARK))

        assertNull(exit.concat(FactTypeChecker.Dummy, delta), "nothing else was attached")
    }

    @Test
    fun `an unrelated mark passes the annotated node untouched`() {
        val exit = abstractFact().deepCleaned(MARK)
        val delta = deltaOf(concreteFact(FIELD_F, MARK_2))

        val applied = exit.concat(FactTypeChecker.Dummy, delta)

        assertNotNull(applied)
        assertTrue(
            applied.readAccessor(FIELD_F)?.startsWithAccessor(MARK_2) == true,
            "the claim is per-mark, not a blanket"
        )
    }

    /* ---------- the annotation is positional ---------- */

    @Test
    fun `the annotation survives a prepend and stays confined to its branch`() {
        // wrap: p.raw = b (before the clean), p.val = b (after it) — one merged exit tree
        val raw = abstractFact().prependAccessor(FIELD_RAW) as AccessTree
        val cleanedVal = abstractFact().deepCleaned().prependAccessor(FIELD_VAL) as AccessTree
        val exit = merged(raw, cleanedVal)

        val delta = deltaOf(concreteFact(FIELD_F, MARK))
        val applied = exit.concat(FactTypeChecker.Dummy, delta)

        assertNotNull(applied, "the unsanitized branch keeps the fact alive")
        assertTrue(applied.readsMarkAt(FIELD_RAW, FIELD_F), "the sibling branch has no claim: the mark attaches")
        assertFalse(applied.readsMarkAt(FIELD_VAL, FIELD_F), "the cleaned branch blocks the same mark")
    }

    @Test
    fun `an annotated node one accessor deep blocks even a direct mark`() {
        // an abstract node below a field of the base: everything under it is already below one
        // accessor of the cleaned base, so the claim applies from relative depth 1
        val innerCleaned = abstractFact().deepCleaned().prependAccessor(FIELD_VAL) as AccessTree
        val cleaned = innerCleaned.deepCleaned() // the prepended tree cleaned at ITS base

        val delta = deltaOf(concreteFact(MARK))
        val applied = cleaned.readAccessor(FIELD_VAL)?.concat(FactTypeChecker.Dummy, delta)

        assertNull(applied, "a direct mark below a non-base abstract node is at base depth >= 2")
    }

    /* ---------- the claim survives a summary transit ---------- */

    @Test
    fun `the empty delta carries the claim onto the transited summary's exit fact`() {
        // the cleaned abstract fact passes through an unrelated callee's identity summary:
        // delta vs the callee's abstract initial is empty, and the callee's exit abstraction
        // continues the same object, so the claim must arrive on it
        val cleanedCallerFact = abstractFact().deepCleaned()
        val calleeExit = abstractFact()

        val emptyDelta = cleanedCallerFact.delta(manager.mostAbstractInitialAp(base)).single { it.isEmpty }
        val transited = calleeExit.concat(FactTypeChecker.Dummy, emptyDelta) as AccessTree?

        assertNotNull(transited)
        assertEquals(
            cleanedCallerFact.access.abstraction,
            transited.access.abstraction,
            "the caller's claim must ride the empty delta onto the exit abstraction"
        )
    }

    @Test
    fun `the transit unions the caller claim with the callee's own`() {
        // the caller had cleaned m when the callee's summary, continuing the same object,
        // cleaned n: both claims hold on this execution
        val cleanedCallerFact = abstractFact().deepCleaned(MARK)
        val calleeExit = abstractFact().deepCleaned(MARK_2)

        val emptyDelta = cleanedCallerFact.delta(manager.mostAbstractInitialAp(base)).single { it.isEmpty }
        val transited = calleeExit.concat(FactTypeChecker.Dummy, emptyDelta) as AccessTree?

        assertNotNull(transited)
        val claim = assertNotNull(transited.access.abstraction)
        assertTrue(with(manager) { MARK.idx } in claim, "the caller's mark is still claimed")
        assertTrue(with(manager) { MARK_2.idx } in claim, "the callee's mark is claimed too")
    }

    /* ---------- joining alternative executions ---------- */

    @Test
    fun `merging cleaned and uncleaned alternatives at the same node drops the claim`() {
        val cleaned = abstractFact().deepCleaned()
        val uncleaned = abstractFact()
        val joined = merged(cleaned, uncleaned)

        assertNull(joined.access.abstraction, "the join of cleaned and uncleaned is uncleaned")

        val delta = deltaOf(concreteFact(FIELD_F, MARK))
        val applied = joined.concat(FactTypeChecker.Dummy, delta)
        assertNotNull(applied)
        assertTrue(applied.readsMarkAt(FIELD_F), "the uncleaned alternative's materialization must not be blocked")
    }

    @Test
    fun `merging two cleaned alternatives intersects their claims`() {
        val cleanedBoth = abstractFact().deepCleaned(MARK).deepCleaned(MARK_2)
        val cleanedM = abstractFact().deepCleaned(MARK)
        val joined = merged(cleanedBoth, cleanedM)

        val delta = deltaOf(merged(concreteFact(FIELD_F, MARK), concreteFact(FIELD_F, MARK_2)))
        val applied = joined.concat(FactTypeChecker.Dummy, delta)

        assertNotNull(applied)
        assertFalse(applied.readsMarkAt(FIELD_F), "m is claimed by both alternatives: blocked")
        assertTrue(
            applied.readAccessor(FIELD_F)?.startsWithAccessor(MARK_2) == true,
            "n is claimed by one alternative only: it must survive the join"
        )
    }

    @Test
    fun `the join is symmetric`() {
        val a = abstractFact().deepCleaned(MARK).deepCleaned(MARK_2)
        val b = abstractFact().deepCleaned(MARK)

        assertEquals(
            merged(a, b).access.abstraction,
            merged(b, a).access.abstraction,
            "the stored claim must not depend on merge order"
        )
    }

    @Test
    fun `merging equal claims is identity`() {
        val a = abstractFact().deepCleaned()
        val b = abstractFact().deepCleaned()

        assertEquals(a.access.abstraction, merged(a, b).access.abstraction)
    }

    /* ---------- persistence ---------- */

    @Test
    fun `the annotation survives a serialization round-trip`() {
        // the sibling shape: an annotated branch and a plain one, in one tree
        val fact = merged(
            abstractFact().deepCleaned().prependAccessor(FIELD_VAL) as AccessTree,
            abstractFact().prependAccessor(FIELD_RAW) as AccessTree,
        )

        val context = object : org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext {
            private val byId = mutableMapOf<Long, Accessor>()
            private val byAccessor = mutableMapOf<Accessor, Long>()
            private var next = 1L

            override fun getIdByAccessor(accessor: Accessor): Long =
                byAccessor.getOrPut(accessor) { (next++).also { byId[it] = accessor } }

            override fun getAccessorById(id: Long): Accessor = byId.getValue(id)
            override fun getIdByMethod(method: org.opentaint.ir.api.common.CommonMethod): Long = error("unused")
            override fun getMethodById(id: Long): org.opentaint.ir.api.common.CommonMethod = error("unused")
            override fun loadSummaries(method: org.opentaint.ir.api.common.CommonMethod): ByteArray? = null
            override fun storeSummaries(method: org.opentaint.ir.api.common.CommonMethod, summaries: ByteArray) = Unit
            override fun flush() = Unit
        }

        val serializer = AccessTree.AccessNode.Serializer(manager, context)
        val bytes = java.io.ByteArrayOutputStream()
        with(serializer) { java.io.DataOutputStream(bytes).writeAccessNode(fact.access) }
        val read = with(serializer) {
            java.io.DataInputStream(java.io.ByteArrayInputStream(bytes.toByteArray())).readAccessNode()
        }

        assertEquals(fact.access, read, "the annotated and the plain branch must both round-trip")
        assertNotNull(read.getChild(with(manager) { FIELD_VAL.idx })?.abstraction)
        assertNull(read.getChild(with(manager) { FIELD_RAW.idx })?.abstraction)
    }
}
