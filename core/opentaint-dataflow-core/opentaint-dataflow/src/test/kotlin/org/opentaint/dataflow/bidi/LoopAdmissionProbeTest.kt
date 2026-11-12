package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class LoopAdmissionProbeTest {
    private val f = StoreFixtures()
    private val policy = RestrictedInitialPolicy(3, 8, Direction.FORWARD, f.manager.marks)
    private val scope = BlockScope(BlockId(1), PortId(2))
    private val primary = InitialEmission(f.pattern(tail = Tail.STAR), Layer.DEMAND)
    private val companion = InitialEmission(primary.pattern.copy(fact = primary.pattern.fact.copy(mark = MarkSlot.STAR)), Layer.NORMAL)
    private val descriptor = LoopAdmissionDescriptor(scope, LoopAdmissionFamily.REPEAT, primary.pattern, primary.layer)
    private var emitted = 0
    private var queries = 0

    private fun view(values: List<InitialEmission>, supported: Boolean = true) = object : ScopeDemandView, LocalAdmissionView {
        override fun supportsScan(actual: Facts, policy: RestrictedInitialPolicy) = supported
        override fun visitInitialEmissions(actual: Facts, policy: RestrictedInitialPolicy, visit: (InitialEmission) -> DemandVisit): DemandScan {
            queries++
            for (value in values) {
                emitted++
                if (visit(value) == DemandVisit.STOP) return DemandScan.STOPPED
            }
            return DemandScan.COMPLETED
        }
        override fun initials(actual: Facts, policy: RestrictedInitialPolicy): Set<AdmittedInitial> =
            values.mapTo(LinkedHashSet()) { AdmittedInitial(f.manager.initial(it.pattern), it.layer) }
        override fun intersect(exit: PortId, original: PremiseKey, raw: Facts, policy: RestrictedInitialPolicy) = emptyList<Facts>()
        override fun acceptsTarget(exit: PortId, original: PremiseKey, policy: RestrictedInitialPolicy) = false
    }
    private fun consumer(view: ScopeDemandView, family: LoopAdmissionFamily = LoopAdmissionFamily.REPEAT,
                         at: BlockScope = scope) = LoopAdmissionConsumer(at, family, view) { true }

    @Test fun `late extra companion stops the entire trial and never scans another consumer`() {
        val v = view(listOf(primary, companion, primary))
        val probe = probeLoopAdmissions(f.manager, policy, f.fact(), setOf(descriptor),
            listOf(consumer(v), consumer(v, LoopAdmissionFamily.ADJACENT)), null, LoopQueryCounts())
        val rejected = assertIs<LoopAdmissionProbe.Rejected>(probe)
        assertEquals(companion.pattern, rejected.extra.pattern)
        assertEquals(2, emitted)
        assertEquals(1, queries)
    }

    @Test fun `same geometry at another physical scope or layer is an extra`() {
        for (different in listOf(descriptor.copy(scope = scope.copy(entry = PortId(9))),
                                 descriptor.copy(layer = Layer.NORMAL),
                                 descriptor.copy(family = LoopAdmissionFamily.ADJACENT))) {
            assertIs<LoopAdmissionProbe.Rejected>(probeLoopAdmissions(f.manager, policy, f.fact(), setOf(different),
                listOf(consumer(view(listOf(primary)))), null, LoopQueryCounts()))
        }
    }

    @Test fun `preflight rejects an unsupported route before any scan`() {
        val supported = view(listOf(primary))
        val unsupported = view(emptyList(), supported = false)
        assertSame(LoopAdmissionProbe.Unsupported, probeLoopAdmissions(f.manager, policy, f.fact(), setOf(descriptor),
            listOf(consumer(supported), consumer(unsupported)), null, LoopQueryCounts()))
        assertEquals(0, queries)
        assertEquals(0, emitted)
    }

    @Test fun `completed bundle retains exact complete labels and reuses cached answer`() {
        val v = view(listOf(primary, companion))
        val scratch = LoopQueryScratch(f.manager, LoopQueryCounts())
        val actual = f.fact()
        assertNull(scratch.peekInitials(v, actual, policy))
        assertEquals(0, queries)
        val native = scratch.initials(v, actual, policy)
        val expected = native.mapTo(HashSet()) {
            LoopAdmissionDescriptor(scope, LoopAdmissionFamily.REPEAT, it.initial.toPattern(), it.layer)
        }
        val complete = assertIs<LoopAdmissionProbe.Complete>(probeLoopAdmissions(f.manager, policy, actual, expected,
            listOf(consumer(v)), scratch, LoopQueryCounts()))
        assertEquals(native, complete.bundle.repeat())
        assertEquals(native.mapTo(HashSet()) { LoopLabelledAdmission(scope, LoopAdmissionFamily.REPEAT, it) },
            complete.bundle.labelled().toSet())
        assertEquals(0, queries, "A complete cached C2 answer must avoid another scan")
    }

    @Test fun `missing-only admissions still need full enclosing observation`() {
        val initial = AdmittedInitial(f.manager.initial(primary.pattern), primary.layer)
        val baseline = LoopObservation(listOf(initial), listOf("needed"), emptyList(),
            listOf(LoopLabelledAdmission(scope, LoopAdmissionFamily.ADJACENT, initial)))
        var full = 0
        var reused: LoopAdmissionBundle? = null
        val bundle = LoopAdmissionBundle.fromDescriptors(f.manager, emptyList())
        val session = LoopRestrictionSession(f.ops, policy, { baseline },
            probe = { _, _ -> LoopAdmissionProbe.Complete(bundle) },
            observeCompleted = { _, completed ->
                full++; reused = completed
                LoopObservation<String>(emptyList(), listOf("needed"), emptyList())
            }, precision = { null })
        assertNotEquals(baseline, session.trial(f.fact(), baseline))
        assertEquals(1, full)
        assertSame(bundle, reused)
    }

    @Test fun `negative probe skips full observation while unsupported keeps it`() {
        var full = 0
        val baseline = LoopObservation<String>(emptyList(), listOf("needed"), emptyList())
        val reject = LoopRestrictionSession(f.ops, policy, { full++; baseline },
            probe = { _, _ -> LoopAdmissionProbe.Rejected(descriptor) }, precision = { null })
        assertNull(reject.trial(f.fact(), baseline))
        assertEquals(0, full)
        val fallback = LoopRestrictionSession(f.ops, policy, { full++; baseline },
            probe = { _, _ -> LoopAdmissionProbe.Unsupported }, precision = { null })
        assertEquals(baseline, fallback.trial(f.fact(), baseline))
        assertEquals(1, full)
    }
    @Test fun `one scalar baseline descriptor set is reused across all budgets`() {
        val initial = AdmittedInitial(f.manager.initial(primary.pattern), primary.layer)
        val baseline = LoopObservation<String>(emptyList(), listOf("enclosing"), listOf(initial),
            listOf(LoopLabelledAdmission(scope, LoopAdmissionFamily.REPEAT, initial)))
        val seen = arrayListOf<Set<LoopAdmissionDescriptor>>()
        val session = LoopRestrictionSession(f.ops, policy, { baseline },
            probe = { _, expected -> seen += expected; LoopAdmissionProbe.Rejected(descriptor) },
            precision = { null })
        repeat(3) { session.trial(f.fact(), baseline) }
        assertEquals(3, seen.size)
        assertSame(seen[0], seen[1])
        assertSame(seen[1], seen[2])
        val other = LoopObservation<String>(emptyList(), listOf("changed"), emptyList())
        session.trial(f.fact(), other)
        assertNotSame(seen[2], seen[3])
        assertTrue(seen[3].isEmpty())
    }

}
