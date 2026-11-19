package org.opentaint.dataflow.bidi

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.ap.ExclusionSet
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.*
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Two programs have the same repeated FLOW guide and different uses of it. */
class RepeatedDemandHiddenRenameTest {
    @Test
    fun `the same repeated guide is necessary only with the latent rename`() {
        val common = setOf("common T sink")
        assertEquals(common, run(extra = false, cut = false))
        assertEquals(common, run(extra = false, cut = true))
        assertEquals(common + "delayed U sink", run(extra = true, cut = false))
        assertEquals(common, run(extra = true, cut = true))
    }

    private fun run(extra: Boolean, cut: Boolean): Set<String> = DriverFixtures().use { f ->
        val p = f.program
        val main = p.method("main", listOf(listOf(1),listOf(2),listOf(3),listOf(4),listOf(5),listOf(6),emptyList()),6).key()
        val helper = p.method("helper", listOf(listOf(1),listOf(2),emptyList()),2).key()
        val before = AccessPathBase.LocalVar(0)
        val localP = AccessPathBase.LocalVar(1)
        val localRet = AccessPathBase.LocalVar(2)
        val after = AccessPathBase.LocalVar(3)
        val arg = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        // Declare exactly the same vocabulary in both worlds, before adding any edge.
        val bytes = p.field("bytes")
        val element = f.manager.accessors.index(ElementAccessor)
        val g = p.field("g")
        val outF = p.field("f")
        val depth = (1..8).map { p.field("d$it") }
        val t = MarkSlot.Concrete(p.mark("T"))
        val u = MarkSlot.Concrete(p.mark("U"))
        fun summary(vararg edges: PathEdge) = f.summary(*edges)
        fun gen(base: AccessPathBase, path: List<Int>, tail: Tail, mark: MarkSlot) =
            PathEdge(ZERO_FACT, PathFact(base,path,tail,mark),ExclusionSet.Empty)
        val sourceU = gen(before,depth + listOf(bytes,g),Tail.EXACT,u)
        p.entry(main,RuleStatement(summary(ZERO_KEEP,sourceU),StatementSummary.EMPTY,emptyList()))
        p.statement(main,1,summary(starEdge(before,depth,localP,emptyList())))
        val sourceT = gen(localP,emptyList(),Tail.ANY_TAINT,t)
        p.call(main,2,CallPlan(setOf(localP),listOf(
            CallStage.Edges(BEFORE,BOUND,BIND_IN,summary(keepEdge(localP),ZERO_KEEP)),
            CallStage.Edges(BOUND,ADDED,SOURCES,summary(keepEdge(localP),ZERO_KEEP,sourceT)),
            CallStage.Edges(ADDED,AFTER,BIND_BACK,summary(keepEdge(localP),ZERO_KEEP))
        ),emptyList(),BEFORE,AFTER))
        p.call(main,3,CallPlan(setOf(localP,localRet),listOf(
            CallStage.Edges(BEFORE,BOUND,BIND_IN,summary(starEdge(localP,emptyList(),arg,emptyList()),ZERO_KEEP)),
            CallStage.Actions(BOUND,ADDED,emptyList()),
            CallStage.Callees(ADDED,RETURNED,listOf(helper)),
            CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
            CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,summary(starEdge(ret,emptyList(),localRet,emptyList()),ZERO_KEEP))
        ),emptyList(),BEFORE,AFTER))
        val sinkT=SinkRule(f.rule("common T sink"),0,listOf(p.pattern(localRet,mark=t)),emptyList())
        p.call(main,4,CallPlan(setOf(localRet),listOf(
            CallStage.Edges(BEFORE,BOUND,BIND_IN,summary(keepEdge(localRet),ZERO_KEEP)),
            CallStage.Actions(BOUND,ADDED,emptyList()),
            CallStage.Edges(ADDED,RETURNED,UNRESOLVED,summary(keepEdge(localRet),ZERO_KEEP)),
            CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
            CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,summary(keepEdge(localRet),ZERO_KEEP))
        ),listOf(sinkT),BEFORE,AFTER))
        p.statement(main,5,summary(keepEdge(localRet),starEdge(localRet,emptyList(),after,depth)))
        val sinkU=SinkRule(f.rule("delayed U sink"),0,listOf(p.pattern(after,depth + outF,mark=u)),emptyList())
        p.exit(main,6,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,listOf(sinkU)),false,emptySet()))
        val sharedEdges=listOf(
            starEdge(arg,emptyList(),ret,emptyList()),
            starEdge(arg,listOf(bytes),ret,emptyList()),
            starEdge(arg,emptyList(),ret,listOf(bytes)),
            starEdge(arg,listOf(bytes,element),ret,emptyList()),
            starEdge(arg,emptyList(),ret,listOf(bytes,element)))
        val hidden=starEdge(arg,listOf(bytes,g),ret,listOf(outF))
        p.statement(helper,1,summary(*(sharedEdges + if(extra) listOf(hidden) else emptyList()).toTypedArray()))
        val selected=DemandPattern(p.pattern(ret,tail=Tail.ANY,mark=MarkSlot.STAR),p.pattern(arg,tail=Tail.STAR,mark=MarkSlot.STAR))
        var repeatedHandoffs = 0
        var removedOrigins = 0
        val driver = f.driver(IncreasingLimits, budget = 15.seconds, run1MarkMode = MarkMode.FULL,
            guardBarrier = { _, body ->
                val next = body()
                if (next !is Next.Run || next.config.index !in listOf(4, 6)) next
                else {
                    val config = next.config
                    assertEquals(listOf(selected), checkNotNull(config.demand).explicitRows(helper))
                    repeatedHandoffs++
                    if (!cut || config.index == 4) next
                    else {
                        val demand = rebuildHandoff(f, Direction.FORWARD) { origin ->
                            val drop = origin.owner == HandoffOwner(helper) && origin.rows ==
                                listOf(PairedDemand(DemandEntry.Data(selected.entry), DemandExit.Data(checkNotNull(selected.exit))))
                            if (drop) removedOrigins++
                            drop
                        }
                        assertTrue(demand.explicitRows(helper).isEmpty())
                        Next.Run(RunConfig(config.index, config.fieldLimit, demand, config.records, config.seeds,
                            config.roots, config.disableRun1Statics, config.run1MarkMode, config.fieldLimitSchedule,
                            config.normalTargets))
                    }
                }
            })
        val report = driver.analyze(listOf(main))
        for (run in listOf(3, 5)) {
            val frontier = driver.frontiers.single { it.run == run }
            assertEquals(mapOf(main to 1, helper to 1), frontier.demandEdges)
        }
        assertEquals(2, repeatedHandoffs)
        assertEquals(if (cut) 1 else 0, removedOrigins)
        assertEquals(RunStatus.COMPLETE, report.end.status)
        assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
        return report.entries.map { entry ->
            assertFalse(entry.provisional)
            entry.descriptor.key.ruleId
        }.toSet()
    }
}
