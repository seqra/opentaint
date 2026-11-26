package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.Seed
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import kotlin.test.*

/**
 * R1 of spec/backward-condition-progress-implementation.md §4: a backward sink seed is NORMAL only if its
 * literal is unary and has the `$` tail (Lean BackCondImpl.code_normal_iff).
 */
class BackwardSeedLayerTest {
    private val owner = FormOwner()
    private val reportRule = object : CommonTaintConfigurationSink {
        override val id = "layer sink"
        override val meta = object : CommonTaintConfigurationSinkMeta {
            override val message = "layer sink"
            override val severity = CommonTaintConfigurationSinkMeta.Severity.Error
        }
    }
    private val a: AccessPathBase = AccessPathBase.Argument(0)
    private val b: AccessPathBase = AccessPathBase.Argument(1)
    private val c: AccessPathBase = AccessPathBase.Argument(2)

    private fun literals(f: MethodAnalysisFixtures): List<Pattern> = listOf(
        f.pattern(a),
        f.pattern(b, tail = Tail.ANY, mark = MarkSlot.Concrete(f.mark("U"))),
        f.pattern(c),
    )

    private fun predicateSink(f: MethodAnalysisFixtures, root: (RulePredicate.Builder, List<Int>) -> Int): SinkRule {
        val builder = RulePredicate.Builder(f.cancellation)
        val leaves = literals(f).map(builder::leaf)
        val predicate = builder.build(root(builder, leaves))
        val id = RuleOccurrenceId(FormKey(owner, f.key.method, f.key, f.inst(2)), RuleKind.CALL_SINK, 0)
        return SinkRule(reportRule, 0, predicate.leaves, emptyList(), id, predicate)
    }

    private fun backward(f: MethodAnalysisFixtures, sinks: List<SinkRule>, seeds: List<Seed>): RunMethodLocalServices {
        f.exitRules(2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, sinks), false, emptySet()))
        lateinit var service: RunMethodLocalServices
        f.core(index = 2, seeds = SeedIndex.of(seeds),
            localFactory = MethodLocalServicesFactory { actor -> RunMethodLocalServices(actor).also { service = it } })
        return service
    }

    private fun layers(emitted: List<Facts>): Map<AccessPathBase, Layer> {
        val result = HashMap<AccessPathBase, Layer>()
        for (facts in emitted) check(result.put(facts.base, facts.layer) in listOf(null, facts.layer)) { "one layer per base" }
        return result
    }

    private fun predicateLayers(root: (RulePredicate.Builder, List<Int>) -> Int): Map<AccessPathBase, Layer> =
        MethodAnalysisFixtures().use { f ->
            val sink = predicateSink(f, root)
            val service = backward(f, listOf(sink),
                listOf(Seed.PredicateSink(checkNotNull(sink.occurrenceId), f.key, f.inst(2))))
            val emitted = ArrayList<Facts>()
            service.fireSinkSeeds(f.inst(2), emitted::add)
            layers(emitted)
        }

    @Test fun `K1 a unary exact predicate literal seeds NORMAL`() {
        assertEquals(mapOf(a to Layer.NORMAL), predicateLayers { _, l -> l[0] })
    }

    @Test fun `K3 an ND exact predicate literal seeds DEMAND`() {
        assertEquals(mapOf(a to Layer.DEMAND, b to Layer.DEMAND), predicateLayers { bld, l -> bld.and(listOf(l[0], l[1])) })
    }

    @Test fun `K5 a literal that is unary in one alternative and ND in another seeds NORMAL`() {
        assertEquals(mapOf(a to Layer.NORMAL, b to Layer.DEMAND), predicateLayers { bld, l ->
            bld.or(listOf(l[0], bld.and(listOf(l[0], l[1]))))
        })
    }

    @Test fun `S-H4 a literal that the DNF repeats stays NORMAL`() {
        // (a or b) and (a or c): the DNF has the alternative a and a, with the literal set {a}.
        assertEquals(mapOf(a to Layer.NORMAL, b to Layer.DEMAND, c to Layer.DEMAND), predicateLayers { bld, l ->
            bld.and(listOf(bld.or(listOf(l[0], l[1])), bld.or(listOf(l[0], l[2]))))
        })
    }

    @Test fun `an OR of unary literals keeps each one NORMAL and the any literal DEMAND`() {
        assertEquals(mapOf(a to Layer.NORMAL, b to Layer.DEMAND, c to Layer.NORMAL),
            predicateLayers { bld, l -> bld.or(listOf(l[0], l[1], l[2])) })
    }

    @Test fun `legacy sink is unary when some alternative of the same rule has the literal alone`() {
        for (unaryAlternative in listOf(true, false)) MethodAnalysisFixtures().use { f ->
            val (la, lb) = literals(f)
            val sinks = buildList {
                if (unaryAlternative) add(SinkRule(reportRule, 0, listOf(la), emptyList()))
                add(SinkRule(reportRule, 1, listOf(la, lb), emptyList()))
            }
            val service = backward(f, sinks, listOf(Seed.Sink(reportRule, f.key, f.inst(2), la),
                Seed.Sink(reportRule, f.key, f.inst(2), lb)))
            val emitted = ArrayList<Facts>()
            service.fireSinkSeeds(f.inst(2), emitted::add)
            assertEquals(mapOf(a to if (unaryAlternative) Layer.NORMAL else Layer.DEMAND, b to Layer.DEMAND),
                layers(emitted), "unary alternative=$unaryAlternative")
        }
    }

    @Test fun `legacy unary reads only alternatives of the seed rule`() {
        MethodAnalysisFixtures().use { f ->
            val (la, lb) = literals(f)
            val other = object : CommonTaintConfigurationSink {
                override val id = "other sink"
                override val meta = reportRule.meta
            }
            val sinks = listOf(SinkRule(other, 0, listOf(la), emptyList()), SinkRule(reportRule, 0, listOf(la, lb), emptyList()))
            val service = backward(f, sinks, listOf(Seed.Sink(reportRule, f.key, f.inst(2), la)))
            val emitted = ArrayList<Facts>()
            service.fireSinkSeeds(f.inst(2), emitted::add)
            assertEquals(mapOf(a to Layer.DEMAND), layers(emitted))
        }
    }

    @Test fun `K7 a legacy ND trigger seeds its exact literal DEMAND and a unary trigger NORMAL`() {
        MethodAnalysisFixtures().use { f ->
            val (la, lb) = literals(f)
            val nd = SinkRule(reportRule, 0, listOf(la, lb), emptyList())
            val service = backward(f, listOf(nd), emptyList())
            val emitted = ArrayList<Facts>()
            service.fireTriggerSeeds(f.inst(2), nd, emitted::add)
            assertEquals(mapOf(a to Layer.DEMAND, b to Layer.DEMAND), layers(emitted))
        }
        MethodAnalysisFixtures().use { f ->
            val (la) = literals(f)
            val unary = SinkRule(reportRule, 0, listOf(la), emptyList())
            val service = backward(f, listOf(unary), emptyList())
            val emitted = ArrayList<Facts>()
            service.fireTriggerSeeds(f.inst(2), unary, emitted::add)
            assertEquals(mapOf(a to Layer.NORMAL), layers(emitted))
        }
    }

    @Test fun `K7 a predicate trigger uses the predicate flag`() {
        MethodAnalysisFixtures().use { f ->
            val sink = predicateSink(f) { bld, l -> bld.and(listOf(l[0], l[2])) }
            val service = backward(f, listOf(sink), emptyList())
            val emitted = ArrayList<Facts>()
            service.fireTriggerSeeds(f.inst(2), sink, emitted::add)
            assertEquals(mapOf(a to Layer.DEMAND, c to Layer.DEMAND), layers(emitted))
        }
    }
}
