package org.opentaint.dataflow.jvm.ap.ifds.alias

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.jvm.BasicTestUtils
import org.opentaint.dataflow.jvm.ap.ifds.AliasAnalysisMode
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.cfg.JIRCallInst
import org.opentaint.ir.api.jvm.cfg.JIRLocalVar
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.ir.api.jvm.ext.findClass
import org.opentaint.ir.impl.features.usagesExt
import org.opentaint.jvm.graph.JApplicationGraphImpl
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

/**
 * Tests of the `SHADOW` mode of the facade and of the alias statistics (IMPL §8).
 *
 * In `SHADOW` mode both backends run, and the consumers get the DSU answers. The statistics record
 * both answers of each query. The statistics must not change an answer.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class AliasShadowModeTest : BasicTestUtils() {
    private val languageManager by lazy { JIRLanguageManager(cp) }
    private val graph by lazy { JApplicationGraphImpl(cp, runBlocking { cp.usagesExt() }) }

    @BeforeEach
    fun resetStats() {
        AliasStats.reset()
    }

    private fun facade(method: JIRMethod, params: JIRLocalAliasAnalysis.Params): JIRLocalAliasAnalysis {
        val callResolver = JIRCallResolver(cp, SingleLocationUnit(method.enclosingClass.declaration.location))
        val reachability = JIRLocalVariableReachability(method, graph, languageManager)
        val cancellation = Cancellation().also { it.activate() }
        return JIRLocalAliasAnalysis(
            method.instList.first(), graph, callResolver, null, reachability, cancellation, languageManager, params,
        )
    }

    private fun params(mode: AliasAnalysisMode, depth: Int = 0) =
        JIRLocalAliasAnalysis.Params(mode = mode, aliasAnalysisInterProcCallDepth = depth)

    private fun method(className: String, name: String): JIRMethod =
        cp.findClass(className).declaredMethods.single { it.name == name }

    private fun probeCall(method: JIRMethod): JIRCallInst =
        method.instList.filterIsInstance<JIRCallInst>().first { it.callExpr.method.name == PROBE }

    private fun probeLocal(call: JIRCallInst, arg: Int): AccessPathBase.LocalVar =
        AccessPathBase.LocalVar((call.callExpr.args[arg] as JIRLocalVar).index)

    /** One query of each kind for each local operand of each call of [method]. */
    private fun queries(method: JIRMethod): List<Pair<JIRCallInst, AccessPathBase.LocalVar>> =
        method.instList.filterIsInstance<JIRCallInst>().flatMap { call ->
            call.callExpr.args.filterIsInstance<JIRLocalVar>().map { call to AccessPathBase.LocalVar(it.index) }
        }

    private fun answersOf(aa: JIRLocalAliasAnalysis, queries: List<Pair<JIRCallInst, AccessPathBase.LocalVar>>) =
        queries.map { (call, base) ->
            listOf(
                aa.findAlias(base, call),
                aa.findAliasAfterStatement(base, call),
                aa.findArrayElementAliases(base, call),
            )
        }

    @Test
    fun `shadow mode gives the DSU answers`() {
        var checked = 0
        for (className in listOf(SAMPLE, INTER_PROC_SAMPLE, STATS_SAMPLE)) {
            for (method in cp.findClass(className).declaredMethods) {
                if (method.instList.size == 0) continue
                val queries = queries(method)
                if (queries.isEmpty()) continue
                for (depth in listOf(0, 1)) {
                    val dsu = answersOf(facade(method, params(AliasAnalysisMode.DSU, depth)), queries)
                    val shadow = answersOf(facade(method, params(AliasAnalysisMode.SHADOW, depth)), queries)
                    assertEquals(dsu, shadow, "${method.name} depth $depth")
                    checked += queries.size
                }
            }
        }
        assertTrue(checked > 100, "Too few queries: $checked")
        AliasStats.summaryLines().filter { "group=shadow" in it || "group=backend" in it }.forEach(::println)
        assertEquals(0L, AliasStats.shadow.directedFailures.sum())
    }

    @Test
    fun `dsu mode answers do not change with the statistics`() {
        val method = method(SAMPLE, "fieldWriteThroughJoinAllocs")
        val queries = queries(method)
        val facadeAnswers = answersOf(facade(method, params(AliasAnalysisMode.DSU)), queries)
        val dsu = JIRDsuAliasAnalysis(
            method.instList.first(), graph,
            JIRCallResolver(cp, SingleLocationUnit(method.enclosingClass.declaration.location)),
            null, JIRLocalVariableReachability(method, graph, languageManager),
            Cancellation().also { it.activate() }, languageManager, params(AliasAnalysisMode.DSU),
        )
        val rawAnswers = queries.map { (call, base) -> dsu.findAlias(base, call) }
        assertEquals(rawAnswers, facadeAnswers.map { it[0] })
        assertTrue(AliasStats.volume.of(AliasBackend.DSU, AliasQueryKind.BEFORE).queries.sum() > 0)
        assertEquals(0L, AliasStats.volume.of(AliasBackend.DIRECTED, AliasQueryKind.BEFORE).queries.sum())
    }

    @Test
    fun `shadow mode records both answer sizes`() {
        val method = method(SAMPLE, "fieldWriteThroughJoinAllocs")
        val call = probeCall(method)
        val z = probeLocal(call, 0)
        val dsuAnswer = assertNotNull(facade(method, params(AliasAnalysisMode.DSU)).findAlias(z, call))
        val directedAnswer = assertNotNull(facade(method, params(AliasAnalysisMode.DIRECTED)).findAlias(z, call))
        AliasStats.reset()

        val shadow = facade(method, params(AliasAnalysisMode.SHADOW))
        assertEquals(dsuAnswer, shadow.findAlias(z, call))
        // A repeated query is recorded one time.
        assertEquals(dsuAnswer, shadow.findAlias(z, call))

        val s = AliasStats.shadow.of(AliasQueryKind.BEFORE)
        assertEquals(1L, s.queries.sum())
        assertEquals(dsuAnswer.size.toLong(), s.dsuAnswers.sum())
        assertEquals(directedAnswer.size.toLong(), s.directedAnswers.sum())
        assertEquals(dsuAnswer.accessorSum(), s.dsuAccessors.sum())
        assertEquals(directedAnswer.accessorSum(), s.directedAccessors.sum())

        val dsuVolume = AliasStats.volume.of(AliasBackend.DSU, AliasQueryKind.BEFORE)
        val directedVolume = AliasStats.volume.of(AliasBackend.DIRECTED, AliasQueryKind.BEFORE)
        assertEquals(1L, dsuVolume.queries.sum())
        assertEquals(1L, directedVolume.queries.sum())
        assertEquals(dsuAnswer.size.toLong(), dsuVolume.answers.sum())
        assertEquals(directedAnswer.size.toLong(), directedVolume.answers.sum())
        assertEquals(1L, AliasStats.backend(AliasBackend.DSU).methods.sum())
        assertEquals(1L, AliasStats.backend(AliasBackend.DIRECTED).methods.sum())
        assertEquals(1L, AliasStats.directed.methods.sum())
        assertTrue(AliasStats.directed.stmtEvals.sum() > 0)
        assertTrue(AliasStats.directed.nodeCount.sum() > 0)
    }

    @Test
    fun `shadow mode records a query where the directed answer is not a subset of the DSU answer`() {
        // The DSU drops the field alias at the unknown call `touch(x)`. The directed call is passive.
        val method = method(SAMPLE, "loadThenUnknownCallLocal")
        val call = probeCall(method)
        val w = probeLocal(call, 0)
        val dsuAnswer = facade(method, params(AliasAnalysisMode.DSU)).findAlias(w, call)
        AliasStats.reset()
        val linesBefore = AliasStats.shadow.diffLines.get()

        val shadow = facade(method, params(AliasAnalysisMode.SHADOW))
        assertEquals(dsuAnswer, shadow.findAlias(w, call))

        val s = AliasStats.shadow.of(AliasQueryKind.BEFORE)
        assertEquals(1L, s.notSubset.sum())
        assertEquals(0L, s.equal.sum())
        // The diff lines have a limit for each process. Other tests can reach it.
        val expectedLines = minOf(linesBefore + 1, AliasShadowStats.MAX_DIFF_LINES)
        assertEquals(expectedLines, AliasStats.shadow.diffLines.get())

        val extra = listOf<AliasInfo>(AliasApInfo(AccessPathBase.LocalVar(1), emptyList()))
        val line = AliasShadowStats.diffLine("m()", 3, AliasQueryKind.AFTER, 2, emptyList(), extra, extra)
        assertTrue(line.startsWith("ALIAS-SHADOW-DIFF method=m() inst=3 kind=AFTER var=local#2 "), line)
        assertTrue(line.contains(" extra=["), line)
    }

    @Test
    fun `a directed failure in shadow mode keeps the DSU answer`() {
        val method = method(SAMPLE, "fieldWriteThroughJoinAllocs")
        val queries = queries(method)
        val dsu = answersOf(facade(method, params(AliasAnalysisMode.DSU)), queries)
        AliasStats.reset()

        // A negative K is not valid: the directed analysis fails when it starts.
        val failing = params(AliasAnalysisMode.SHADOW).copy(symDepth = -1)
        assertEquals(dsu, answersOf(facade(method, failing), queries))
        assertEquals(1L, AliasStats.shadow.directedFailures.sum())
        assertEquals(0L, AliasStats.shadow.of(AliasQueryKind.BEFORE).queries.sum())
    }

    @Test
    fun `directed volume counts the paths that share only null-valued origins with the query`() {
        val unwritten = method(STATS_SAMPLE, "readOfUnwrittenField")
        val unwrittenCall = probeCall(unwritten)
        val a = facade(unwritten, params(AliasAnalysisMode.DIRECTED)).findAlias(probeLocal(unwrittenCall, 0), unwrittenCall)
        assertEquals(1, assertNotNull(a).size)
        val volume = AliasStats.volume.of(AliasBackend.DIRECTED, AliasQueryKind.BEFORE)
        assertEquals(1L, volume.nullOnlyPaths.sum())

        val written = method(STATS_SAMPLE, "readOfWrittenField")
        val writtenCall = probeCall(written)
        val b = facade(written, params(AliasAnalysisMode.DIRECTED)).findAlias(probeLocal(writtenCall, 0), writtenCall)
        assertTrue(assertNotNull(b).isNotEmpty())
        assertEquals(1L, volume.nullOnlyPaths.sum())
        assertEquals(2L, volume.queries.sum())
    }

    @Test
    fun `the summary lines have the stable format and parse back`() {
        val method = method(SAMPLE, "loadThenUnknownCallLocal")
        val call = probeCall(method)
        val shadowParams = params(AliasAnalysisMode.SHADOW)
        facade(method, shadowParams).findAlias(probeLocal(call, 0), call)

        val lines = AliasStats.summaryLines(shadowParams)
        val parsed = lines.map { line ->
            assertTrue(line.startsWith("ALIAS-STATS group="), line)
            AliasStats.parseSummaryLine(line)
        }
        val byGroup = parsed.groupBy { it.getValue("group") }
        val config = byGroup.getValue("config").single()
        assertEquals("SHADOW", config["mode"])
        assertEquals("7", config["symDepth"])
        assertEquals("6", config["maxAccessors"])
        assertEquals("10000", config["maxCallClosure"])
        assertEquals("0", config["depth"])

        val backends = byGroup.getValue("backend").associateBy { it.getValue("backend") }
        assertEquals("1", backends.getValue("DSU")["methods"])
        assertEquals("1", backends.getValue("DIRECTED")["methods"])

        val shadowBefore = byGroup.getValue("shadow").single { it["kind"] == "BEFORE" }
        assertEquals("1", shadowBefore["queries"])
        assertEquals("1", shadowBefore["notSubset"])
        assertEquals(
            setOf("BEFORE", "AFTER", "ARRAY_ELEMENT", "HEAP", "ALL"),
            byGroup.getValue("shadow").map { it["kind"] }.toSet()
        )

        val volume = byGroup.getValue("volume")
        assertEquals(10, volume.size)
        val directedBefore = volume.single { it["backend"] == "DIRECTED" && it["kind"] == "BEFORE" }
        assertEquals("1", directedBefore["queries"])
        assertEquals("na", volume.single { it["backend"] == "DSU" && it["kind"] == "BEFORE" }["nullOnlyPaths"])

        val directed = byGroup.getValue("directed").single()
        assertEquals("1", directed["methods"])
        for (key in DIRECTED_KEYS) {
            for (suffix in listOf("Sum", "P50", "P99", "Max")) {
                assertTrue(directed.getValue(key + suffix).toLong() >= 0, "$key$suffix")
            }
        }
        assertTrue(directed.getValue("stmtEvalsSum").toLong() > 0)
        assertTrue(directed.getValue("callsSum").toLong() > 0)

        val origins = byGroup.getValue("directedOrigins").single()
        assertTrue(origins.getValue("symByDepth").split(',').all { it.substringAfter(':').toLong() >= 0 })
        assertTrue(byGroup.containsKey("directedCalls"))
        assertTrue(byGroup.containsKey("shadowRun"))
        assertTrue(byGroup.containsKey("volumeMethods"))

        for (map in parsed) {
            for ((key, value) in map) {
                if (key in TEXT_KEYS) continue
                assertTrue(value.toLongOrNull() != null, "$key=$value in ${map["group"]}")
            }
        }
    }

    private fun List<AliasInfo>.accessorSum(): Long =
        filterIsInstance<AliasApInfo>().sumOf { it.accessors.size }.toLong()

    private class SingleLocationUnit(val loc: RegisteredLocation) : JIRUnitResolver {
        override fun resolve(method: JIRMethod): UnitType =
            if (method.enclosingClass.declaration.location == loc) SingletonUnit else UnknownUnit

        override fun locationIsUnknown(loc: RegisteredLocation): Boolean = loc != this.loc
    }

    private companion object {
        const val SAMPLE = "sample.alias.DirectedAliasSample"
        const val INTER_PROC_SAMPLE = "sample.alias.InterProcAliasSample"
        const val STATS_SAMPLE = "sample.alias.AliasStatsSample"
        const val PROBE = "probe"

        val TEXT_KEYS = setOf("group", "mode", "backend", "kind", "symByDepth", "nullOnlyPaths")

        val DIRECTED_KEYS = listOf(
            "stmtEvals", "headIterations", "headIterationsMax", "nodeCount", "contentSize", "memoHits",
            "memoMisses", "retires", "calls", "callFallbacks", "inlinedCalls", "etreeSize", "evalSize",
            "retainedEntries", "fixpointTimeUs",
        )
    }
}
