package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FieldLimitSchedule
import org.opentaint.dataflow.bidi.driver.Seed
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import kotlin.test.*

/** Exercise ordinary AP admission, not only the numeric schedule selector. */
class FieldLimitScheduleAdmissionTest {
    private val sink = object : CommonTaintConfigurationSink {
        override val id = "run-index deeper static seed"
        override val meta = object : CommonTaintConfigurationSinkMeta {
            override val message = id
            override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
        }
    }

    private fun config(f: MethodAnalysisFixtures, schedule: FieldLimitSchedule, demand: DemandStore,
                       seeds: SeedIndex = SeedIndex.EMPTY) =
        RunConfig(2, schedule.fieldLimit(2), demand, f.records, seeds, listOf(f.key),
            fieldLimitSchedule = schedule)

    @Test fun `run2 current limit admits a deeper static input under the old coarse concrete demand`() {
        for (schedule in FieldLimitSchedule.entries) MethodAnalysisFixtures().use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val nested = path + f.field("nested")
            val oldDemand = f.pattern(STATIC, path, Tail.ANY)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(oldDemand, oldDemand))
            }.build()
            val actor = f.core(config(f, schedule, demand))
            val actual = f.fact(STATIC, nested, Tail.EXACT, layer = Layer.DEMAND)

            actor.addLink(CallerRef(f.key, f.manager.zero, actual.layer, f.inst(1)), actual.layer, actual)

            val expected = if (schedule == FieldLimitSchedule.RUN_INDEX)
                f.pattern(STATIC, nested, Tail.EXACT) else oldDemand
            assertEquals(setOf(f.manager.initial(expected)), actor.initials.all().toSet())
            assertEquals(nested, f.ops.leaves(actual).single().fact.path,
                "The configured cut must not mutate the supplied actual value")
        }
    }

    @Test fun `run2 seed uses the current limit before strict static input validation`() {
        for (schedule in FieldLimitSchedule.entries) MethodAnalysisFixtures().use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val requirement = f.pattern(STATIC, path + f.field("nested"), Tail.EXACT)
            val demand = DemandStore.Builder(f.manager).build()
            val seed = Seed.Sink(sink, f.key, f.inst(2), requirement)
            val actor = f.core(config(f, schedule, demand, SeedIndex.of(listOf(seed))),
                localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val emitted = ArrayList<Facts>()

            actor.localServices.fireSinkSeeds(f.inst(2), emitted::add)

            val expected = if (schedule == FieldLimitSchedule.RUN_INDEX) requirement
                else f.pattern(STATIC, path, Tail.ANY, requirement.fact.mark)
            assertEquals(listOf(expected), emitted.flatMap { f.ops.leaves(it).toList() })
            assertEquals(if (schedule == FieldLimitSchedule.RUN_INDEX) Layer.NORMAL else Layer.DEMAND,
                emitted.single().layer)
        }
    }

    @Test fun `C2 abstract old demand does not invent a concrete mark at the larger limit`() {
        MethodAnalysisFixtures().use { f ->
            val path = listOf(f.field("f"))
            val coarse = f.pattern(AccessPathBase.Argument(0), path, Tail.ANY, MarkSlot.STAR)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(coarse, coarse))
            }.build()
            val actual = f.fact(AccessPathBase.Argument(0), path + f.field("nested"), Tail.EXACT,
                layer = Layer.DEMAND)
            val actor = f.core(config(f, FieldLimitSchedule.RUN_INDEX, demand))

            actor.addLink(CallerRef(f.key, f.manager.zero, actual.layer, f.inst(1)), actual.layer, actual)

            val expected = f.pattern(AccessPathBase.Argument(0), path, Tail.STAR, MarkSlot.STAR)
            assertEquals(setOf(f.manager.initial(expected)), actor.initials.all().toSet())
        }
    }

    @Test fun `C5 old coarse pair keeps deeper current result and rejects the wrong original mark`() {
        MethodAnalysisFixtures().use { f ->
            val retPath = listOf(f.field("returned"))
            val argPath = listOf(f.field("argument"))
            val entry = f.pattern(AccessPathBase.Return, retPath, Tail.ANY)
            val exit = f.pattern(AccessPathBase.Argument(0), argPath, Tail.ANY)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(entry, exit))
            }.build()
            val config = config(f, FieldLimitSchedule.RUN_INDEX, demand)
            val original = f.manager.initial(f.pattern(AccessPathBase.Return,
                retPath + f.field("nestedReturn"), Tail.EXACT))
            val raw = f.fact(AccessPathBase.Argument(0), argPath + f.field("nestedArgument"),
                Tail.EXACT, layer = Layer.DEMAND)

            assertEquals(2, config.fieldLimit)
            assertEquals(listOf(raw), demand.intersect(f.key, original, raw),
                "A run-1 ANY endpoint admits the matching run-2 exact descendant")
            val wrong = f.manager.initial(original.toPattern().let {
                it.copy(fact = it.fact.copy(mark = MarkSlot.Concrete(f.mark("U"))))
            })
            assertTrue(demand.intersect(f.key, wrong, raw).isEmpty(),
                "A deeper geometry must not bypass the fixed entry-mark gate")
        }
    }
}
