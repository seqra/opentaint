package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.SinkRule
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.Record
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.PairedDemand
import org.opentaint.dataflow.bidi.store.DemandEntry
import org.opentaint.dataflow.bidi.store.DemandExit
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** A native component counterexample, not a whole-program iteration run.
 * The demand snapshot and saved record are explicit test inputs. Production
 * code and the selected C2 policy are unchanged. No completion is added.
 */
class LoopSavedRepeatGateDiagnosisTest {
    private val fixture = MethodAnalysisFixtures()
    @AfterTest fun closeFixture() = fixture.close()

    private val ap = fixture.manager
    private val ops = fixture.ops
    private val x = AccessPathBase.Argument(0)
    private val f = fixture.field("f")
    private val t = MarkSlot.Concrete(fixture.mark("T"))
    private val mode = ApMode(false, Direction.FORWARD, 4)
    private val policy = RestrictedInitialPolicy(5, 4, Direction.FORWARD, ap.marks)
    private val repeat = BlockScope(BlockId(2), PortId(5))
    private val parent = BlockScope.ROOT
    private val exactDemand = fixture.pattern(x, listOf(f), mark = t)
    private val demandStore = DemandStore.Builder(ap).apply {
        add(fixture.key, repeat, PortId(11), PairedDemand(DemandEntry.Data(exactDemand), DemandExit.Zero))
        add(fixture.key, BlockScope(BlockId(2), PortId(1)), PortId(5),
            PairedDemand(DemandEntry.Zero, DemandExit.Data(fixture.pattern(x, listOf(f, f), Tail.STAR, t))))
    }.build()
    private val readInitial = ap.initial(fixture.pattern(x, listOf(f), Tail.STAR, MarkSlot.STAR))
    private val readOutput = fixture.fact(x, tail = Tail.STAR, mark = MarkSlot.STAR)
    private val readEdge = PathEdge(readInitial.toPattern().fact,
        ops.leaves(readOutput).single().fact, ExclusionSet.Empty)
    private val savedRead by lazy {
        val results = ArrayList<Facts>()
        ops.applyEdge(ops.startFact(readInitial), readInitial, readEdge, true, mode, object : ApOut {
            override fun result(f: Facts) { results += f }
            override fun markRequest(mark: TaintMark) = error("A FLOW read has no mark condition")
        })
        assertEquals(readOutput, results.single())
        Record(fixture.key, Direction.FORWARD, readInitial, results.single(), repeat, PortId(5))
    }
    private val application = LocalRelationApplication(ops, mode)

    private fun fact(depth: Int, layer: Layer = Layer.NORMAL) =
        fixture.fact(x, List(depth) { f }, mark = t, layer = layer)

    private fun admissions(value: Facts): Set<AdmittedInitial> =
        demandStore.scope(fixture.key, repeat).initials(value, policy).toSet()

    @Test fun `actual ZERO source and read survive paired C5 before the loop gate`() {
        fun apply(actual: Facts, edge: PathEdge): Facts {
            val result = ArrayList<Facts>()
            ops.applyEdge(actual, ap.zero, edge, true, mode, object : ApOut {
                override fun result(f: Facts) { result += f }
                override fun markRequest(mark: TaintMark) = error("No source request")
            })
            return result.single()
        }
        val source = PathEdge(ap.zero.toPattern().fact,
            fixture.pattern(x, List(4) { f }, mark = t).fact, ExclusionSet.Empty)
        val marked = apply(Reach.NORMAL, source)
        assertEquals(fact(4), marked)
        val afterRead = apply(marked, readEdge)
        assertEquals(fact(3), afterRead)
        val firstEntry = BlockScope(BlockId(2), PortId(1))
        assertEquals(listOf(afterRead), demandStore.scope(fixture.key, firstEntry)
            .intersect(PortId(5), ap.zero, afterRead, policy))
        assertTrue(admissions(afterRead).isEmpty())
    }

    // Runtime observe() supplies adjacent saved records here, not repeat saved records.
    private fun observer() = LoopConsumerObservation(ops, mode, LoopConsumerViews(
        parent, false, { emptySet() }, ::admissions, { emptySequence() },
        { _, _ -> emptySequence() }, { _, _, value -> listOf(value) },
        { _, _ -> false }, { _, _ -> false }, { true }))

    private fun replay(value: Facts): Facts {
        val results = ArrayList<Facts>()
        application.applyRecord(value, ap.zero, savedRead, object : LocalRelationOut {
            override fun data(original: PremiseKey, value: Facts) {
                assertSame(ap.zero, original)
                results += value
            }
            override fun target(original: PremiseKey, target: Target) = error("A read is not a Target")
            override fun markRequest(mark: TaintMark) = error("A concrete input needs no mark request")
        })
        return results.single()
    }

    @Test fun `gate drops NORMAL GEN before an applicable saved repeat read`() {
        val raw = fact(3)
        val gate = LoopOutputRestriction(ops)
        assertTrue(loopSummaryGrows(ap.zero, ops.leaves(raw).single()))
        assertTrue(observer().observe(ap.zero, raw).isEmpty)
        val kept = gate.restrict(false, ap.zero, ops.leaves(raw).single(), raw) { observer().observe(ap.zero, it) }
        assertTrue(kept.isEmpty())
        assertEquals(1L, gate.statistics.drops)
        assertEquals(0L, gate.statistics.trials, "The fact is dropped before any prefix trial")
        assertEquals(fact(2), replay(raw), "The omitted repeat saved relation has a real NORMAL effect")
    }

    @Test fun `saved first repeat delivery reaches existing exact admission without completion`() {
        val gate = LoopOutputRestriction(ops)
        var value = fact(3)
        assertTrue(admissions(value).isEmpty())
        for (depth in listOf(2, 1)) {
            val applied = replay(value)
            value = gate.restrict(false, readInitial, ops.leaves(readOutput).single(), applied) {
                error("The stored 1-to-0 read must bypass the growth gate")
                @Suppress("UNREACHABLE_CODE") LoopObservation<String>(emptyList(), emptyList(), emptyList())
            }.single()
            assertEquals(fact(depth), value)
        }
        assertEquals(setOf(AdmittedInitial(ap.initial(exactDemand), Layer.NORMAL)), admissions(value))
        assertEquals(2L, gate.statistics.bypasses)
        assertEquals(0L, gate.statistics.observations)
    }

    @Test fun `existing NormalTarget joins preserve ZERO origin in both arrival orders`() {
        val actual = replay(replay(fact(3)))
        val admitted = admissions(actual).single()
        // Execute x=x.f and the real CM(x.$,T) predicate for this actor.
        val sinkInputs = ArrayList<Facts>()
        ops.applyEdge(actual, admitted.initial, readEdge, true, mode, object : ApOut {
            override fun result(f: Facts) { sinkInputs += f }
            override fun markRequest(mark: TaintMark) = error("A concrete read needs no request")
        })
        val witness = assertIs<MarkCheck.Holds>(ops.checkMark(sinkInputs.single(),
            fixture.pattern(x, mark = t), mode)).facts
        assertEquals(fact(0), witness)
        assertEquals(Layer.NORMAL, witness.layer)
        lateinit var service: RunMethodLocalServices
        val actor = fixture.core(index = 5, L = 4,
            localFactory = MethodLocalServicesFactory { core ->
                RunMethodLocalServices(core).also { service = it }
            })
        val rule = object : CommonTaintConfigurationSink {
            override val id = "saved-repeat-native-sink"
            override val meta = object : CommonTaintConfigurationSinkMeta {
                override val message = "saved repeat exact sink"
                override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
            }
        }
        val sink = SinkRule(rule, 0, listOf(fixture.pattern(x, mark = t)), emptyList())
        val checked = service.checkSinks(admitted.initial, fixture.inst(1), sinkInputs.single(), listOf(sink))
        assertEquals(listOf(sink to Layer.NORMAL), checked.fired)
        val targetRow = actor.targets.single()
        assertSame(admitted.initial, targetRow.premise)
        val id = assertIs<Target.NormalTarget>(targetRow.target)
        for (targetFirst in listOf(false, true)) {
            val targets = ArrayList<Pair<PremiseKey, Target>>()
            val links = BlockSummaryLinks(ops, mode, repeat,
                { _, _, _, _, _, _ -> error("Target-only check") },
                { _, original, target -> targets += original to target },
                { _, _, _ -> error("No request") })
            val link = LocalLink(parent, PortId(5), ap.zero, actual.layer, repeat)
            val rows = listOf(targetRow)
            if (targetFirst) links.publishTargets(rows)
            links.offer(link, actual)
            if (!targetFirst) links.publishTargets(rows)
            while (links.hasPending) links.drain(1)
            assertEquals(listOf<Pair<PremiseKey, Target>>(ap.zero to id), targets)
        }
    }

    @Test fun `DEMAND replay cannot produce a normal witness and an identity is no progress`() {
        val actual = replay(replay(fact(3, Layer.DEMAND)))
        assertEquals(fact(1, Layer.DEMAND), actual)
        val exact = ap.initial(exactDemand)
        assertNull(application.targetArmLayer(actual, exact, Target.NormalTarget(ReportId(29)), saved = false))
        val identity = Record(fixture.key, Direction.FORWARD,
            ap.initial(fixture.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR)), readOutput)
        var result: Facts? = null
        application.applyRecord(fact(3), ap.zero, identity, object : LocalRelationOut {
            override fun data(original: PremiseKey, value: Facts) { result = value }
            override fun target(original: PremiseKey, target: Target) = error("No Target")
            override fun markRequest(mark: TaintMark) = error("No request")
        })
        assertEquals(fact(3), result)
        assertTrue(admissions(assertNotNull(result)).isEmpty())
    }

    // Candidate policy adapter. It changes no production implementation.
    private fun candidateGate(premise: PremiseKey, shape: Pattern, value: Facts): List<Facts> =
        LoopOutputRestriction(ops).restrict(false,
            !premise.isZero && loopSummaryGrows(premise, shape), value) {
                observer().observe(ap.zero, it)
            }

    @Test fun `candidate ZERO bypass delivers source to the existing normal sink route`() {
        val raw = fact(3)
        val delivered = candidateGate(ap.zero, ops.leaves(raw).single(), raw).single()
        assertSame(raw, delivered)
        val exactInput = replay(replay(delivered))
        assertEquals(fact(1), exactInput)
        assertEquals(setOf(AdmittedInitial(ap.initial(exactDemand), Layer.NORMAL)), admissions(exactInput))
        val sinkInput = replay(exactInput)
        assertEquals(fact(0), sinkInput)
        assertIs<MarkCheck.Holds>(ops.checkMark(sinkInput, fixture.pattern(x, mark = t), mode))
    }

    @Test fun `candidate does not confuse enclosing ZERO origin with a DATA summary premise`() {
        // The actual still has parent original ZERO, as in replay() and observer().
        // The stored local relation is x.f.* -> x.f.f.*: DATA, and growing.
        val geometry = fixture.pattern(x, listOf(f, f), Tail.STAR, MarkSlot.STAR)
        assertTrue(candidateGate(readInitial, geometry, fact(3)).isEmpty())
        val demandSupply = fact(3, Layer.DEMAND)
        assertSame(demandSupply, candidateGate(ap.zero, ops.leaves(demandSupply).single(), demandSupply).single())
    }

    @Test fun `candidate still applies the global bound before the ZERO bypass`() {
        val raw = fact(3)
        var bounded: Facts? = null
        ops.limit(raw, 2, object : ApOut {
            override fun result(f: Facts) { bounded = f }
            override fun markRequest(mark: TaintMark) = error("A field limit cannot request a mark")
        })
        val kept = candidateGate(ap.zero, ops.leaves(raw).single(), assertNotNull(bounded)).single()
        assertEquals(fixture.fact(x, listOf(f, f), Tail.ANY, t, layer = Layer.DEMAND), kept)
        assertEquals(Layer.DEMAND, kept.layer)
    }

}
