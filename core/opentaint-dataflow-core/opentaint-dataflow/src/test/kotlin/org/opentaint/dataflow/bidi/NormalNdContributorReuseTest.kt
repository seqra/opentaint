package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.Seed
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** Real local rule services accept the old certificates; no saved contributor row is hand-built. */
class NormalNdContributorReuseTest {
    private val owner = FormOwner()
    private val left = AccessPathBase.Argument(0)
    private val right = AccessPathBase.Argument(1)
    private val returned = AccessPathBase.Return
    private val reportRule = object : CommonTaintConfigurationSink {
        override val id = "retained ND contributor sink"
        override val meta = object : CommonTaintConfigurationSinkMeta {
            override val message = id
            override val severity = CommonTaintConfigurationSinkMeta.Severity.Error
        }
    }

    private data class Actor(val core: RunMethodAnalyzer, val services: RunMethodLocalServices)
    private data class Output(val premise: PremiseKey, val facts: Facts)

    private fun atom(f: MethodAnalysisFixtures, name: String) = MarkSlot.Concrete(f.mark(name))
    private fun pattern(f: MethodAnalysisFixtures, base: AccessPathBase) =
        f.pattern(base, mark = atom(f, if (base == right) "U" else "T"))
    private fun fact(f: MethodAnalysisFixtures, base: AccessPathBase, layer: Layer = Layer.NORMAL) =
        f.fact(base, mark = atom(f, if (base == right) "U" else "T"), layer = layer)
    private fun premise(f: MethodAnalysisFixtures, base: AccessPathBase) = f.manager.initial(pattern(f, base))

    private fun predicate(f: MethodAnalysisFixtures): RulePredicate {
        val builder = RulePredicate.Builder(f.cancellation, f.manager.marks)
        return builder.build(builder.and(listOf(builder.leaf(pattern(f, left)), builder.leaf(pattern(f, right)))))
    }

    private fun occurrence(f: MethodAnalysisFixtures, kind: RuleKind, ordinal: Int = 0) =
        RuleOccurrenceId(FormKey(owner, f.key.method, f.key, f.inst(1)), kind, ordinal)

    private fun source(f: MethodAnalysisFixtures): SourceRuleOccurrence {
        val id = occurrence(f, RuleKind.CALL_SOURCE)
        return SourceRuleOccurrence(id, predicate(f), listOf(SourceAction(ActionId(id, ActionRole.SOURCE, 0),
            f.pattern(returned, mark = atom(f, "V")).fact)))
    }

    private fun sink(f: MethodAnalysisFixtures, ordinal: Int = 0): SinkRule {
        val condition = predicate(f)
        return SinkRule(reportRule, 0, condition.leaves, emptyList(),
            occurrence(f, RuleKind.CALL_SINK, ordinal), condition)
    }

    private fun permissions(f: MethodAnalysisFixtures, source: SourceRuleOccurrence) =
        SeedIndex.of(source.predicate.leaves.map { leaf ->
            val action = source.actions.single()
            Seed.Source(f.key, f.inst(1), source.transfer(leaf, action, multi = true).forward, action.id)
        })

    private fun actor(f: MethodAnalysisFixtures, run: Int, seeds: SeedIndex = SeedIndex.EMPTY): Actor {
        lateinit var services: RunMethodLocalServices
        val config = RunConfig(run, maxOf(1, run - 1),
            if (run == 1) null else DemandStore.Builder(f.manager).build(),
            f.records, seeds, listOf(f.key), run1MarkMode = MarkMode.FULL)
        val core = f.core(config, localFactory = MethodLocalServicesFactory {
            RunMethodLocalServices(it).also { local -> services = local }
        })
        return Actor(core, services)
    }

    private fun publishCompleted(f: MethodAnalysisFixtures, previous: Actor) {
        f.drain(previous.core)
        previous.core.freeze()
        f.shared.normalRuleContributors.publish(previous.core.normalContributorRows().asIterable())
    }

    private fun at(f: MethodAnalysisFixtures, base: AccessPathBase, stage: Int,
                   layer: Layer = Layer.NORMAL, original: PremiseKey = premise(f, base)): OperationInput {
        // BlockRunState's transient operation owner changes between actors.
        // A fresh owner here also checks that the stable site uses the physical
        // operation and stage, rather than retaining the old runtime owner.
        val operation = OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(1)), stageOrdinal = stage)
        return OperationInput(ResumeSite.CallStageInput(operation), original, fact(f, base, layer))
    }

    private fun acceptSource(f: MethodAnalysisFixtures, current: Actor, source: SourceRuleOccurrence,
                             base: AccessPathBase, outputs: MutableList<Output>,
                             layer: Layer = Layer.NORMAL, site: OperationInput? = null,
                             original: PremiseKey = premise(f, base), facts: Facts = fact(f, base, layer)) {
        if (site == null) current.services.sourcePredicate(source, original, facts, f.inst(1), false) { p, value ->
            outputs += Output(p, value)
        } else current.services.sourcePredicateAt(source, original, facts, f.inst(1), false, site) { p, value ->
            outputs += Output(p, value)
        }
    }

    @Test fun `an incomplete NORMAL source leaf survives and keeps current layer and protection`() {
        for (layer in listOf(Layer.NORMAL, Layer.DEMAND)) MethodAnalysisFixtures().use { f ->
            val rule = source(f)
            val previous = actor(f, 1)
            val outputs = ArrayList<Output>()
            val oldFact = fact(f, left) as TaintTree
            acceptSource(f, previous, rule, left, outputs, facts = oldFact.withProtection(oldFact.root))
            assertTrue(outputs.isEmpty(), "One accepted leaf cannot complete the source")
            publishCompleted(f, previous)
            assertTrue(previous.core.normalContributorRows().any())

            val current = actor(f, 3, permissions(f, rule))
            acceptSource(f, current, rule, right, outputs, layer)
            val result = outputs.single()
            assertEquals(setOf(premise(f, left), premise(f, right)), result.premise.members.toSet())
            assertEquals(layer, result.facts.layer)
            assertEquals(returned, result.facts.base)
            assertNotNull((result.facts as TaintTree).nonSubsumable,
                "The restored checked leaf must retain its protection metadata")
            assertEquals(atom(f, "V"), f.ops.leaves(result.facts).single().fact.mark)
            acceptSource(f, current, rule, right, outputs, layer)
            assertEquals(1, outputs.size, "Restoring or accepting the same support twice adds no result")
        }
    }

    @Test fun `a previous DEMAND source leaf is not a retained NORMAL certificate`() {
        MethodAnalysisFixtures().use { f ->
            val rule = source(f)
            val outputs = ArrayList<Output>()
            val previous = actor(f, 1)
            acceptSource(f, previous, rule, left, outputs, Layer.DEMAND)
            publishCompleted(f, previous)
            assertTrue(previous.core.normalContributorRows().none())
            acceptSource(f, actor(f, 3, permissions(f, rule)), rule, right, outputs)
            assertTrue(outputs.isEmpty())
        }
    }

    @Test fun `restored source supports do not replace the current source permission check`() {
        MethodAnalysisFixtures().use { f ->
            val rule = source(f)
            val outputs = ArrayList<Output>()
            val previous = actor(f, 1)
            acceptSource(f, previous, rule, left, outputs)
            publishCompleted(f, previous)
            val current = actor(f, 3, SeedIndex.EMPTY)
            acceptSource(f, current, rule, right, outputs)
            assertTrue(outputs.isEmpty(), "A valid old guard is not a new source-action permission")
        }
    }

    @Test fun `an old complete cube activates only on a current accepted check and emits once`() {
        MethodAnalysisFixtures().use { f ->
            val rule = source(f)
            val outputs = ArrayList<Output>()
            val previous = actor(f, 1)
            acceptSource(f, previous, rule, left, outputs)
            acceptSource(f, previous, rule, right, outputs)
            assertTrue(outputs.isNotEmpty(), "The prior complete rule must be genuinely evaluated")
            publishCompleted(f, previous)
            outputs.clear()
            val current = actor(f, 3, permissions(f, rule))
            assertTrue(outputs.isEmpty(), "Constructing the actor does not replay a rule")
            current.services.sourcePredicate(rule, f.manager.zero,
                f.fact(returned, mark = atom(f, "V")), f.inst(1), false) { p, value -> outputs += Output(p, value) }
            assertTrue(outputs.isEmpty(), "A packet which matches no leaf does not activate the snapshot")
            acceptSource(f, current, rule, left, outputs)
            assertEquals(1, outputs.size, "A complete imported binding cannot be lost to duplicate current input")
            assertEquals(setOf(premise(f, left), premise(f, right)), outputs.single().premise.members.toSet())
            assertEquals(Layer.NORMAL, outputs.single().facts.layer)
            acceptSource(f, current, rule, left, outputs)
            acceptSource(f, current, rule, right, outputs)
            assertEquals(1, outputs.size)
        }
    }

    @Test fun `source stages have separate restored and current live joins`() {
        MethodAnalysisFixtures().use { f ->
            val rule = source(f)
            val outputs = ArrayList<Output>()
            val previous = actor(f, 1)
            acceptSource(f, previous, rule, left, outputs, site = at(f, left, 2))
            publishCompleted(f, previous)
            val current = actor(f, 3, permissions(f, rule))
            acceptSource(f, current, rule, left, outputs, site = at(f, left, 2))
            assertTrue(outputs.isEmpty(), "Restoring leaf P does not invent Q")
            acceptSource(f, current, rule, right, outputs, site = at(f, right, 3))
            assertTrue(outputs.isEmpty(), "Stage 3 cannot complete the restored stage-2 condition")
            acceptSource(f, current, rule, right, outputs, site = at(f, right, 2))
            assertEquals(1, outputs.size)
        }
    }

    @Test fun `a rebuilt legacy conjunction reuses accepted NORMAL support without a compiled edge key`() {
        MethodAnalysisFixtures().use { f ->
            fun edge() = ConjunctiveEdge(listOf(pattern(f, left), pattern(f, right)),
                f.pattern(returned, mark = atom(f, "V")).fact)
            val oldEdge = edge()
            val outputs = ArrayList<Output>()
            val previous = actor(f, 1)
            previous.services.conjunction(oldEdge, premise(f, left), fact(f, left), f.inst(1)) { p, value ->
                outputs += Output(p, value)
            }
            assertTrue(outputs.isEmpty())
            publishCompleted(f, previous)
            val rebuilt = edge()
            assertNotSame(oldEdge, rebuilt)
            val current = actor(f, 3)
            current.services.conjunction(rebuilt, premise(f, right), fact(f, right, Layer.DEMAND), f.inst(1)) { p, value ->
                outputs += Output(p, value)
            }
            val output = outputs.single()
            assertEquals(setOf(premise(f, left), premise(f, right)), output.premise.members.toSet())
            assertEquals(Layer.DEMAND, output.facts.layer)
            assertEquals(returned, output.facts.base)
        }
    }

    @Test fun `BOUND sink stages reuse the same support and keep current parts local`() {
        MethodAnalysisFixtures().use { f ->
            val rule = sink(f)
            val previous = actor(f, 1)
            val oldAt = at(f, left, 2, original = f.manager.zero)
            assertTrue(previous.services.checkSinksAt(f.manager.zero, f.inst(1), oldAt.facts, listOf(rule), oldAt).fired.isEmpty())
            publishCompleted(f, previous)
            val current = actor(f, 3)
            val now = at(f, right, 9)
            val result = current.services.checkSinksAt(now.premise, f.inst(1), now.facts, listOf(rule), now)
            assertEquals(listOf(rule to Layer.NORMAL), result.fired)
            assertEquals(1, result.parts.size)
            assertEquals(right, result.parts.single().base,
                "Saved SESSION evidence is not a mask for the current DATA packet")
            val target = current.core.targets.single()
            assertEquals(premise(f, right), target.premise)
            assertIs<Target.NormalTarget>(target.target)
            assertFalse(target.premise.isZero)
        }
    }

    @Test fun `retained nonzero sink origin stays conditional and a partial caller cannot report`() {
        MethodAnalysisFixtures().use { f ->
            val rule = sink(f)
            val previous = actor(f, 1)
            assertTrue(previous.services.checkSinks(premise(f, left), f.inst(1), fact(f, left), listOf(rule)).fired.isEmpty())
            publishCompleted(f, previous)
            val current = actor(f, 3)
            current.services.checkSinks(premise(f, right), f.inst(1), fact(f, right), listOf(rule))
            val row = current.core.targets.single()
            assertIs<Target.NormalTarget>(row.target)
            assertEquals(setOf(premise(f, left), premise(f, right)), row.premise.members.toSet())
            assertIs<PremiseSet>(row.premise)

            fun apply(offers: List<Facts>): List<Pair<PremiseKey, Target>> {
                val results = ArrayList<Pair<PremiseKey, Target>>()
                val child = BlockScope(BlockId(1), PortId(4))
                val links = BlockSummaryLinks(f.ops, ApMode(false, Direction.FORWARD, 2), child,
                    { _, _, _, _, _, _ -> fail("This control has only a terminal relation") },
                    { _, original, target -> results += original to target },
                    { _, _, _ -> fail("Concrete caller inputs need no request") })
                links.publishTargets(listOf(row))
                for (offer in offers) links.offer(LocalLink(BlockScope.ROOT, PortId(4),
                    f.manager.zero, offer.layer, child), offer)
                while (links.hasPending) assertTrue(links.drain(1) > 0)
                return results
            }
            assertTrue(apply(listOf(fact(f, right))).isEmpty(),
                "A caller with clean p and only q/U must not borrow the old conditional p/T")
            val good = apply(listOf(fact(f, right), fact(f, left))).single()
            assertTrue(good.first.isZero)
            assertEquals(row.target, good.second)
            assertTrue(apply(listOf(fact(f, right), fact(f, left, Layer.DEMAND))).isEmpty(),
                "NormalTarget still requires every caller member to be NORMAL")
        }
    }
}
