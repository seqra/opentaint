package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.fixtures.TERMINATION_BASELINE_LAST_RUN
import org.opentaint.dataflow.bidi.fixtures.TerminationBaselinePolicy

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Every path symbol below is a separate ordinary instruction, not a
 * supplied summary or a special multi-field pass. The same finite branch
 * definitions generate both the CFG and the complete certificate grammar. */
class WordChunkWriteReadTerminationTest {
    private sealed interface Op {
        data class Move(val from: AccessPathBase,val read: List<Int>,val to: AccessPathBase,val write: List<Int>): Op
        data class Call(val from: AccessPathBase,val to: AccessPathBase): Op
    }
    private fun run(wbase: List<Int>, rbase: List<Int>, repeat: List<List<Int>>, expected: Boolean,
                    mutual: Boolean = false, repair: Boolean = true, nativeExpected: Boolean = expected,
                    writerBefore: List<Int> = emptyList(),
                    readerAround: List<Pair<List<Int>, List<Int>>> = repeat.map { it to emptyList() }) {
        DriverFixtures().use { f ->
            val p = f.program
            val symbols = (1..3).associateWith { p.field("field$it") }
            fun map(word: List<Int>) = word.map(symbols::getValue)
            val wb = map(wbase); val rb = map(rbase); val repeats = repeat.map(::map)
            val main = p.method("word main",listOf(listOf(1),listOf(2),listOf(3),emptyList()),3).key()
            val arg = AccessPathBase.Argument(0); val ret = AccessPathBase.Return
            val x = AccessPathBase.LocalVar(0); val y = AccessPathBase.LocalVar(1); val z = AccessPathBase.LocalVar(2)
            fun body(writer: Boolean,base: List<Int>): List<List<Op>> {
                fun branch(word: List<Int>,recursive: Boolean, eachSide: List<Int> = emptyList()): List<Op> {
                    val out = arrayListOf<Op>(); var value: AccessPathBase = arg; var local = 10
                    if (writer && recursive) {
                        for (symbol in map(writerBefore).asReversed()) {
                            val target = AccessPathBase.LocalVar(local++)
                            out += Op.Move(value, emptyList(), target, listOf(symbol))
                            value = target
                        }
                        val next = AccessPathBase.LocalVar(local++); out += Op.Call(value,next); value = next
                    }
                    for (symbol in if (writer) word.reversed() else word) {
                        val next = AccessPathBase.LocalVar(local++)
                        out += if (writer) Op.Move(value,emptyList(),next,listOf(symbol)) else Op.Move(value,listOf(symbol),next,emptyList())
                        value = next
                    }
                    if (!writer && recursive && eachSide.isEmpty()) {
                        out += Op.Call(value, ret)
                        return out
                    }
                    if (!writer && recursive) {
                        val result = AccessPathBase.LocalVar(local++)
                        out += Op.Call(value, result)
                        value = result
                        for (symbol in eachSide) {
                            val target = AccessPathBase.LocalVar(local++)
                            out += Op.Move(value, listOf(symbol), target, emptyList())
                            value = target
                        }
                    }
                    out += Op.Move(value,emptyList(),ret,emptyList())
                    return out
                }
                return listOf(branch(base,false)) + if (writer) repeats.map { branch(it,true) }
                    else readerAround.map { (before, after) -> branch(map(before), true, map(after)) }
            }
            data class Built(val key: MethodKey,val install: (MethodKey)->Unit)
            fun call(from: AccessPathBase,to: AccessPathBase,callee: MethodKey) = CallPlan(setOf(from),listOf(
                CallStage.Edges(BEFORE,BOUND,BIND_IN,f.summary(ZERO_KEEP,starEdge(from,emptyList(),arg,emptyList()))),
                CallStage.Actions(BOUND,ADDED,emptyList()),CallStage.Callees(ADDED,RETURNED,listOf(callee)),
                CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,f.summary(ZERO_KEEP,starEdge(ret,emptyList(),to,emptyList())))
            ),emptyList(),BEFORE,AFTER)
            fun build(name: String,writer: Boolean,base: List<Int>): Built {
                val branches = body(writer,base)
                val exit = branches.sumOf { it.size }+1
                val graph = MutableList(exit+1) { emptyList<Int>() }
                val placements = arrayListOf<Pair<Int,Op>>()
                val starts = arrayListOf<Int>(); var next = 1
                for (branch in branches) {
                    starts += next
                    branch.forEachIndexed { index,op ->
                        placements += next to op
                        graph[next] = listOf(if (index==branch.lastIndex) exit else next+1)
                        next++
                    }
                }
                graph[0] = starts
                val key = p.method(name,graph,exit).key()
                return Built(key) { callee -> for ((at,op) in placements) when (op) {
                    is Op.Call -> p.call(key,at,call(op.from,op.to,callee))
                    is Op.Move -> p.statement(key,at,StatementSummary(setOf(AccessPathBase.Zero,op.from,op.to),
                        listOf(MicroEdge.of(ZERO_KEEP),MicroEdge.of(keepEdge(op.from)),
                            MicroEdge.of(starEdge(op.from,op.read,op.to,op.write))),emptyList(),emptyMap()))
                } }
            }
            val writer = build("word writer",true,wb); val reader = build("word reader",false,rb)
            val writer2 = if (mutual) build("other word writer",true,wb) else null
            val reader2 = if (mutual) build("other word reader",false,rb) else null
            writer.install(writer2?.key ?: writer.key); writer2?.install?.invoke(writer.key)
            reader.install(reader2?.key ?: reader.key); reader2?.install?.invoke(reader.key)
            val mark = MarkSlot.Concrete(p.mark("T"))
            p.entry(main,RuleStatement(f.summary(ZERO_KEEP,PathEdge(ZERO_FACT,PathFact(x,emptyList(),Tail.EXACT,mark),ExclusionSet.Empty)),StatementSummary.EMPTY,emptyList()))
            p.call(main,1,call(x,y,writer.key)); p.call(main,2,call(y,z,reader.key))
            p.exit(main,3,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,listOf(
                SinkRule(f.rule("word observer"),0,listOf(p.pattern(z,tail=Tail.EXACT,mark=mark)),emptyList()))),false,emptySet()))
            val owners = if (mutual) 2 else 1
            fun grammar(base: List<Int>) = (0 until owners).flatMap { owner ->
                listOf(RegularFieldPathQuery.Clause(owner,base,null)) + repeats.map {
                    RegularFieldPathQuery.Clause(owner,it,if (mutual) 1-owner else owner)
                }
            }
            fun nested(base: List<Int>, around: List<Pair<List<Int>, List<Int>>>) =
                (0 until owners).flatMap { owner ->
                    listOf(NestedFieldPathCertificate.Rule(owner, base, null)) +
                        around.map { (before, after) ->
                            NestedFieldPathCertificate.Rule(owner, before, if (mutual) 1-owner else owner, after)
                        }
                }
            val readRegular = readerAround.all { it.second.isEmpty() }
            val writeRegular = writerBefore.isEmpty()
            val writerGrammar = grammar(wb)
            val readerGrammar = (0 until owners).flatMap { owner ->
                listOf(RegularFieldPathQuery.Clause(owner, rb, null)) +
                    readerAround.map { (before, _) ->
                        RegularFieldPathQuery.Clause(owner, map(before), if (mutual) 1-owner else owner)
                    }
            }
            val certificate = when {
                writeRegular && readRegular -> RegularFieldPathQuery.disjoint(writerGrammar, readerGrammar, owners)
                !repair -> null // Historical diagnostic with only R39 available.
                writeRegular -> RegularFieldPathQuery.compile(owners, writerGrammar)?.let {
                    NestedFieldPathCertificate.disjoint(
                        nested(rb, readerAround.map { (before,after) -> map(before) to map(after) }),
                        owners, it, emptyList(), completeSlice = true,
                    )
                }
                readRegular -> RegularFieldPathQuery.compile(owners, readerGrammar)?.let {
                    NestedFieldPathCertificate.disjoint(
                        nested(wb, repeats.map { it to map(writerBefore) }),
                        owners, it, emptyList(), completeSlice = true,
                    )
                }
                else -> null
            }
            val noRoute = certificate == true
            if (certificate != null) assertEquals(!expected, noRoute)
            var rewrites = 0
            val driver = f.driver(if (repair) IncreasingLimits else TerminationBaselinePolicy,30.seconds,
                run1MarkMode=MarkMode.FULL,invokeRun = { config,owner,timeout ->
                    val previous = f.configs.lastOrNull()
                    val known = previous?.normalTargets?.zeroRows()?.any { it.method==main } == true
                    val actual = if (repair && config.direction==Direction.BACKWARD && previous!=null && !previous.run1 && (noRoute || known)) {
                        rewrites++
                        RunConfig(config.index,config.fieldLimit,withoutCertifiedRootTarget(f,previous,main),config.records,config.seeds,config.roots,
                            run1MarkMode=config.run1MarkMode,fieldLimitSchedule=config.fieldLimitSchedule,normalTargets=config.normalTargets)
                    } else config
                    f.run(actual,owner,timeout)
                })
            val report = driver.analyze(listOf(main))
            println("WORD_CHUNK w=$wbase r=$rbase repeat=$repeat mutual=$mutual before=$writerBefore readerAround=$readerAround repair=$repair end=${report.end} normal=${report.entries.count { !it.provisional }} rewrites=$rewrites")
            if (!repair && report.end.status in setOf(RunStatus.TIMEOUT, RunStatus.OOM)) {
                val completed = driver.frontiers.last()
                println("TERMINATION_BASELINE lastCompleted=${completed.run} targets=${completed.targetDemand}")
                assertTrue(driver.frontiers.any { it.run >= 9 && it.run % 2 == 1 && it.targetDemand > 0 })
                return
            }
            assertEquals(RunStatus.COMPLETE,report.end.status)
            assertTrue(report.end.reason == EndReason.NO_DEMAND_EDGE || (!repair && report.end.reason == EndReason.RUN_LIMIT))
            assertEquals(if (nativeExpected) 1 else 0,report.entries.count { !it.provisional })
            if (expected && !nativeExpected) { assertFalse(noRoute); assertEquals(0,rewrites) }
            if (!repair && writerBefore.isNotEmpty()) {
                assertEquals(5, report.end.run)
                assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
                for (result in f.results) {
                    val actors = result.analyzers.associateBy { it.key }
                    val ownerRows = listOf(writer.key, reader.key).map { key ->
                        actors[key]?.summaries?.all()?.count() ?: 0
                    }
                    val rootTarget = actors[main]?.outgoingTargets?.any { it.premise.isZero } == true
                    println("NESTED_WRITER_CONTROL run=${result.runIndex} rootTarget=$rootTarget ownerRows=$ownerRows")
                }
            }
            if (writerBefore.isEmpty() && !readRegular && !expected && !mutual) {
                assertEquals(if (repair) 5 else TERMINATION_BASELINE_LAST_RUN, report.end.run)
                assertEquals(if (repair) EndReason.NO_DEMAND_EDGE else EndReason.RUN_LIMIT, report.end.reason)
                assertTrue(f.results.filter { it.runIndex in (if (repair) listOf(1,3) else listOf(1,3,5,7,9)) }.all { result ->
                    result.analyzers.single { it.key==main }.outgoingTargets.any { it.premise.isZero }
                })
                assertEquals(if (repair) 1 else 0, rewrites)
            }
        }
    }
    @Test fun `two sided recursive writer diagnostic`() =
        run(listOf(1), listOf(2), listOf(listOf(2)), false, repair=false, writerBefore=listOf(1))
    @Test fun `two sided recursive reader diagnostic`() =
        run(listOf(1), listOf(2), listOf(listOf(2)), false, repair=false,
            readerAround=listOf(listOf(2) to emptyList(), listOf(3) to listOf(3)))
    @Test fun `nested reader certificate closes the cycle`() =
        run(listOf(1), listOf(2), listOf(listOf(2)), false,
            readerAround=listOf(listOf(2) to emptyList(), listOf(3) to listOf(3)))
    @Test fun `nested reader with a real route retains the observation`() =
        run(listOf(1), listOf(1), listOf(listOf(2)), true,
            readerAround=listOf(listOf(2) to emptyList(), listOf(3) to listOf(3)))
    @Test fun `nested reader positive baseline`() =
        run(listOf(1), listOf(1), listOf(listOf(2)), true, repair=false,
            readerAround=listOf(listOf(2) to emptyList(), listOf(3) to listOf(3)))
    @Test fun `only the nested arm supplies the shared path in the baseline`() =
        run(listOf(3,2,3), listOf(2), listOf(listOf(2)), true, repair=false,
            readerAround=listOf(listOf(2) to emptyList(), listOf(3) to listOf(3)))
    @Test fun `certificate preserves the path through the nested arm`() =
        run(listOf(3,2,3), listOf(2), listOf(listOf(2)), true,
            readerAround=listOf(listOf(2) to emptyList(), listOf(3) to listOf(3)))
    @Test fun `same final field terminal chunks retain their earlier natural completion`() = run(listOf(1,3),listOf(2,3),listOf(listOf(2),listOf(3)),false,repair=false)
    @Test fun `complete chunks prove disjointness beyond a last-field check`() = run(listOf(1,3),listOf(2,3),listOf(listOf(2),listOf(3)),false)
    @Test fun `parity negative control retains its earlier natural completion`() = run(listOf(1),listOf(2,1),listOf(listOf(2,2)),false,repair=false)
    @Test fun `regular parity proof stops without suffix enumeration`() = run(listOf(1),listOf(2,1),listOf(listOf(2,2)),false)
    @Test fun `mutual recursive alternatives preserve complete no-route service`() = run(listOf(1),listOf(2),listOf(listOf(2),listOf(3)),false,mutual=true)
    @Test fun `mutual positive recursive alternatives retain the NORMAL relation`() = run(listOf(1),listOf(1),listOf(listOf(2),listOf(3)),true,mutual=true)
    @Test fun `long shared-word baseline diagnostic is unaffected by the certificate`() = run(listOf(1),listOf(2,2,2,2,2,2,1),listOf(listOf(2,2)),true,nativeExpected=false)
    @Test fun `long shared-word baseline has the same pre-existing diagnostic`() = run(listOf(1),listOf(2,2,2,2,2,2,1),listOf(listOf(2,2)),true,repair=false,nativeExpected=false)
    @Test fun `unfused ordinary direct writer-reader diagnostic`() = run(listOf(1),listOf(2),listOf(listOf(2),listOf(3)),false,repair=false)
    @Test fun `unfused ordinary direct writer-reader certificate`() = run(listOf(1),listOf(2),listOf(listOf(2),listOf(3)),false)
}
