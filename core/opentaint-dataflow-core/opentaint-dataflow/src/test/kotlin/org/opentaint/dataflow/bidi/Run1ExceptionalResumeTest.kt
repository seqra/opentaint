package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import kotlin.test.*

class Run1ExceptionalResumeTest {
    @Test fun `late exceptional boundary mark answer checks the sink without publishing a normal summary`() {
        MethodAnalysisFixtures(successors = listOf(listOf(1), emptyList(), emptyList()),
            normalExit = 2, exceptionalExit = 1).use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val atom = f.manager.marks.runtimeAtom(f.mark("T"), MarkMode.GROUP)
            val rule = object : CommonTaintConfigurationSink {
                override val id = "late exceptional sink"
                override val meta = object : CommonTaintConfigurationSinkMeta {
                    override val message = id
                    override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
                }
            }
            val sink = SinkRule(rule, 0, listOf(f.pattern(AccessPathBase.Return,
                mark = MarkSlot.Concrete(atom))), emptyList())
            f.exitRules(1, ExitRules(RuleStatement(StatementSummary.EMPTY,
                StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
            val actor = f.core(localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val initial = f.manager.initial(f.pattern(STATIC, path, Tail.STAR, MarkSlot.STAR))
            val value = f.fact(AccessPathBase.Return, tail = Tail.STAR,
                mark = MarkSlot.STAR, layer = Layer.DEMAND)
            val operation = OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(1)))
            actor.installPoint(initial, value, ResumeSite.StatementInput(operation))
            f.drain(actor)
            assertTrue(f.vulnerabilities.witnessesOf(1).none())
            assertTrue(actor.summaries.all().none())

            val effects = checkNotNull(actor.runnerPort.staticService).commit(StaticBatch().apply {
                supplies += RegionGroups(f.pattern(STATIC, path, Tail.STAR, MarkSlot.STAR), MarkSet.of(atom))
            })
            assertTrue(effects.any { it is StaticOwnerEffect.PointReady && it.owner == actor.key })
            for (effect in effects) if (effect.owner == actor.key) actor.onStaticEffect(effect)
            f.drain(actor)

            assertTrue(f.vulnerabilities.witnessesOf(1).any { it.first.rule == rule })
            assertTrue(actor.summaries.all().none(), "An exceptional resume has no normal-exit summary")
            assertTrue(actor.staticGuidanceSeeds.frozenRows().none())
            assertTrue(f.publications.flatten().isEmpty())
            assertTrue(actor.work(1), "The late reply must finish its exceptional boundary")
        }
    }
}
