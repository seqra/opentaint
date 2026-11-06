package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import kotlinx.coroutines.runBlocking
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
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAllocInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.alias.CallResolver
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRIntraProcAliasAnalysis.JIRInstGraph
import org.opentaint.dataflow.jvm.ap.ifds.alias.Stmt
import org.opentaint.dataflow.jvm.ap.ifds.alias.TaintRulesCallModelProvider
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRCallInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRLocalVar
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.ir.api.jvm.ext.findClass
import org.opentaint.ir.impl.features.usagesExt
import org.opentaint.jvm.graph.JApplicationGraphImpl
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

/**
 * Tests of the inlining of resolved calls on JIR samples (IMPL §5.5, §5.4): the lowering of a
 * resolved call, the callee contexts and sites, the exceptional exit into a caller handler, and
 * the post-fixpoint check of each caller with its inlined callees. Each analysis sets the
 * inlining depth explicitly.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class JIRDirectedInlineTest : BasicTestUtils() {

    private val languageManager by lazy { JIRLanguageManager(cp) }
    private val graph by lazy { JApplicationGraphImpl(cp, runBlocking { cp.usagesExt() }) }

    private fun params(depth: Int) = JIRLocalAliasAnalysis.Params(
        aliasAnalysisInterProcCallDepth = depth,
        mode = AliasAnalysisMode.DIRECTED,
    )

    private fun analyze(method: JIRMethod, depth: Int = 1): DirectedAliasResult {
        val callResolver = JIRCallResolver(cp, SingleLocationUnit(method.enclosingClass.declaration.location))
        val reachability = JIRLocalVariableReachability(method, graph, languageManager)
        val cancellation = Cancellation().also { it.activate() }
        val analysis = JIRDirectedAliasAnalysis(
            method.instList.first(), graph, callResolver, null, reachability, cancellation, languageManager,
            params(depth), verifyPostFix = true,
        )
        return assertNotNull(analysis.compute(), "no result for ${method.name}")
    }

    private fun facade(method: JIRMethod, depth: Int = 1): JIRLocalAliasAnalysis {
        val callResolver = JIRCallResolver(cp, SingleLocationUnit(method.enclosingClass.declaration.location))
        val reachability = JIRLocalVariableReachability(method, graph, languageManager)
        val cancellation = Cancellation().also { it.activate() }
        return JIRLocalAliasAnalysis(
            method.instList.first(), graph, callResolver, null, reachability, cancellation, languageManager, params(depth),
        )
    }

    private fun method(className: String, name: String): JIRMethod =
        cp.findClass(className).declaredMethods.single { it.name == name }

    private inner class Analyzed(val method: JIRMethod, depth: Int = 1) {
        val result = analyze(method, depth)
        val tables get() = result.tables

        fun call(name: String): JIRCallInst =
            method.instList.filterIsInstance<JIRCallInst>().first { it.callExpr.method.name == name }

        fun assignOfCall(name: String, nth: Int = 0): JIRAssignInst =
            method.instList.filterIsInstance<JIRAssignInst>().filter { it.callExpr?.method?.name == name }[nth]

        fun probeLocal(i: Int): JIRLocalVar = call(PROBE).callExpr.args[i] as JIRLocalVar

        fun varOf(local: JIRLocalVar): VarId = tables.vars.local(local.index)

        fun before(inst: JIRInst): AliasState = assertNotNull(result.statesBefore[inst.location.index])

        fun after(inst: JIRInst): AliasState = assertNotNull(result.statesAfter[inst.location.index])

        fun pts(st: AliasState, local: JIRLocalVar): Set<OriginId> =
            tables.nodes.members(st.varNode(varOf(local))).toSet()

        fun argO(i: Int): OriginId = tables.origins.root(tables.bases.arg(i))

        fun instr(inst: JIRInst): AliasInstr = result.cfg.instr(inst.location.index)
    }

    /** The contexts of the locals of [st]. */
    private fun contexts(tables: AliasTables, st: AliasState): Set<Int> {
        val out = HashSet<Int>()
        st.forEachVar { v, _ -> tables.vars.key(v)?.let { out += it.context } }
        return out
    }

    @Test
    fun `post-fixpoint check passes at depth 1 on each method of the samples`() {
        val classes = listOf(
            INLINE, "$INLINE\$Box", "$INLINE\$Thrower",
            DIRECTED, "$DIRECTED\$Box", "$DIRECTED\$Holder", "$DIRECTED\$FinalBox", "$DIRECTED\$CtorLoop",
            "$DIRECTED\$CtorJoin", "$DIRECTED\$ThisWrites", "$DIRECTED\$GenericStatics", "$DIRECTED\$NestedStatics",
            "$DIRECTED\$NestedStatics\$Inner", "$DIRECTED\$Counter",
            "sample.alias.InterProcAliasSample", "sample.alias.HeaderValuesHangSample",
            "sample.alias.FlakyAliasSample", "sample.alias.HeapAliasSample", "sample.alias.LoopAliasSample",
            "sample.alias.SimpleAliasSample",
        )
        var count = 0
        var inlined = 0
        for (className in classes) {
            for (m in cp.findClass(className).declaredMethods) {
                if (m.instList.size == 0) continue
                val result = analyze(m)
                assertTrue(result.tables.nodes.isFrozen)
                inlined += (0 until result.cfg.size).count { result.cfg.instr(it) is AliasInstr.ResolvedCall }
                count++
            }
        }
        assertTrue(count > 80, "only $count methods")
        assertTrue(inlined > 50, "only $inlined resolved calls")
    }

    @Test
    fun `a resolved call is lowered to a resolved call at depth 1 and to an unresolved call at depth 0`() {
        val m = method(INLINE, "twoMakes")
        val depth1 = Analyzed(m, depth = 1)
        val depth0 = Analyzed(m, depth = 0)
        val make = depth1.assignOfCall("make")
        assertIs<AliasInstr.ResolvedCall>(depth1.instr(make))
        assertIs<AliasInstr.UnresolvedCall>(depth0.instr(make))
        assertEquals(1, depth1.result.cfg.callees(make.location.index).size)
    }

    @Test
    fun `callee writes this f then throws and the caller handler sees x f alias a`() {
        val a = Analyzed(method(INLINE, "handlerSeesCalleeWrite"))
        val probe = a.call(PROBE)
        val t = a.probeLocal(0)
        assertTrue(a.argO(0) in a.pts(a.before(probe), t), "t ~ a in the handler")
        assertEquals(setOf(ROOT_CONTEXT), contexts(a.tables, a.before(probe)))

        val answers = facade(a.method).findAlias(AccessPathBase.LocalVar(t.index), probe).orEmpty()
        assertTrue(
            answers.any { it is AliasApInfo && it.base == AccessPathBase.Argument(0) && it.accessors.isEmpty() },
            answers.toString(),
        )
    }

    @Test
    fun `the same callee at two call statements has two contexts and two sites`() {
        val a = Analyzed(method(INLINE, "twoMakes"))
        val probe = a.call(PROBE)
        val st = a.before(probe)
        val pa = a.pts(st, a.probeLocal(0))
        val pb = a.pts(st, a.probeLocal(1))
        val oa = pa.single()
        val ob = pb.single()
        assertTrue(a.tables.origins.isAllocNew(oa) && a.tables.origins.isAllocNew(ob))
        val ka = a.tables.sites.key(a.tables.origins.site(oa))
        val kb = a.tables.sites.key(a.tables.origins.site(ob))
        assertEquals(ka.instIndex, kb.instIndex)
        assertTrue(ka.context != ROOT_CONTEXT && kb.context != ROOT_CONTEXT && ka.context != kb.context)
        assertEquals(setOf(ROOT_CONTEXT), contexts(a.tables, st))

        // A query never reports a callee variable or a callee allocation.
        val answers = facade(a.method).findAlias(AccessPathBase.LocalVar(a.probeLocal(0).index), probe)
        assertEquals(emptyList(), answers)
        assertTrue(answers.orEmpty().none { it is AliasAllocInfo })
    }

    @Test
    fun `a returned null gets the site of the callee return`() {
        val a = Analyzed(method(INLINE, "nullTwice"))
        val st = a.before(a.call(PROBE))
        val na = a.pts(st, a.probeLocal(0)).single()
        val nb = a.pts(st, a.probeLocal(1)).single()
        assertTrue(na != nb)
        val ret = method(INLINE, "nullValue").instList.first { it is JIRReturnInst }
        for (o in listOf(na, nb)) {
            val key = assertIs<BaseKey.Null>(a.tables.bases.key(a.tables.origins.base(o)))
            val site = a.tables.sites.key(key.site)
            assertEquals(ret.location.index, site.instIndex)
            assertTrue(site.context != ROOT_CONTEXT)
        }
    }

    @Test
    fun `a returned caller constant keeps the constant`() {
        val a = Analyzed(method(INLINE, "constantArgument"))
        val ret = a.method.instList.first { it is JIRReturnInst }
        val r = a.method.instList.filterIsInstance<JIRAssignInst>().first { it.callExpr != null }.lhv as JIRLocalVar
        val c = a.tables.origins.root(a.tables.bases.const(STRING_TYPE, "s"))
        assertEquals(setOf(c), a.pts(a.before(ret), r))
    }

    @Test
    fun `the call result joins the returns of the callee`() {
        val a = Analyzed(method(INLINE, "returnsOfOneCallee"))
        val st = a.before(a.call(PROBE))
        assertEquals(setOf(a.argO(0), a.argO(1)), a.pts(st, a.probeLocal(0)))
    }

    @Test
    fun `callee sites are loop sites when the call is in a caller loop`() {
        val a = Analyzed(method(INLINE, "makeInLoop"))
        val make = a.assignOfCall("make")
        val callee = a.result.cfg.callees(make.location.index).single()
        assertTrue(callee.callOnCycle)
        val st = a.before(a.call(PROBE))
        val last = a.pts(st, a.probeLocal(0))
        val sites = last.filter { a.tables.origins.isAllocNew(it) || a.tables.origins.isAllocOld(it) }
            .map { a.tables.origins.site(it) }.toSet()
        assertEquals(1, sites.size)
        val s = sites.single()
        assertTrue(a.tables.sites.isLoopSite(s))
        // The callee object of the last iteration holds the older objects of the site in its next cell.
        val nw = a.tables.origins.allocNew(s)
        val next = a.tables.cells.find("$INLINE\$Box", "next", "$INLINE\$Box")
        val n = st.heapNode(heapKey(nw, next)).takeIf { it != NO_ID } ?: a.tables.origins.defaultNode(nw, next)
        assertTrue(a.tables.origins.allocOld(s) in a.tables.nodes.members(n).toSet(), "the callee object retires in the caller loop")
    }

    @Test
    fun `an unresolved call inside the callee grows Etree of the caller`() {
        val a = Analyzed(method(INLINE, "unresolvedCallInCallee"))
        val passOn = a.call("passOn")
        val etree = a.tables.nodes.members(a.after(passOn).varNode(ETREE)).toSet()
        assertTrue(a.argO(0) in etree, etree.toString())
    }

    /**
     * Main makes the callee context `ContextInfo([k * 1000 + j])` for the override `j` of the call
     * statement `k`. With 1001 overrides, the override 1000 of the statement `k` and the override 0
     * of the statement `k + 1` get equal `ContextInfo` values. The engine must give them two
     * contexts: else the two bodies share their sites, a once-site runs two times, and the store
     * `b.value = y` is a strong update on the object of `a`.
     */
    @Test
    fun `two call bodies with equal context info of main get two engine contexts`() {
        val m = method(INLINE, "twoCallsWithManyOverrides")
        val make = method(INLINE, "make")
        val fail = method(INLINE, "fail")
        val first = m.instList.filterIsInstance<JIRAssignInst>().single { it.callExpr?.method?.name == "makeFirst" }
        val second = m.instList.filterIsInstance<JIRAssignInst>().single { it.callExpr?.method?.name == "makeSecond" }
        assertEquals(first.location.index + 1, second.location.index, "the two calls are consecutive statements")

        // Each wrapper is one more override with the body of `fail`: it always throws.
        val failing = List(1000) { object : JIRMethod by fail {} }
        val overrides = mapOf(
            "makeFirst" to failing + make,
            "makeSecond" to listOf(make) + failing,
        )
        val jirResolver = JIRCallResolver(cp, SingleLocationUnit(m.enclosingClass.declaration.location))
        val base = jirAliasCallResolver(graph, languageManager, jirResolver, TaintRulesCallModelProvider(null), params(1))
        val resolver = object : CallResolver by base {
            override fun resolveMethodCall(callStmt: Stmt.Call, level: Int): List<JIRMethod>? =
                if (level == 0) overrides[callStmt.method.name] else null

            override fun buildMethodGraph(method: JIRMethod): JIRInstGraph? =
                base.buildMethodGraph(if (method in failing) fail else method)
        }

        val tables = AliasTables(params(1).symDepth)
        val cfg = JIRAliasInliner(tables, graph, languageManager, resolver).rootCfg(m.instList.first())
        val result = DirectedFixpoint(AliasTransfer(tables)).run(cfg, verify = true)
        assertEquals(1001, cfg.callees(first.location.index).size)
        assertEquals(1001, cfg.callees(second.location.index).size)

        val probe = m.instList.filterIsInstance<JIRCallInst>().single { it.callExpr.method.name == PROBE }
        val st = assertNotNull(result.statesBefore[probe.location.index])
        fun pts(i: Int): Set<OriginId> {
            val v = tables.vars.local((probe.callExpr.args[i] as JIRLocalVar).index)
            return tables.nodes.members(st.varNode(v)).toSet()
        }
        val oa = pts(1).single()
        val ob = pts(2).single()
        assertTrue(oa != ob, "a and b are two objects")
        val ka = tables.sites.key(tables.origins.site(oa))
        val kb = tables.sites.key(tables.origins.site(ob))
        assertEquals(ka.instIndex, kb.instIndex)
        assertTrue(ka.context != kb.context, "two engine contexts")

        val x = tables.origins.root(tables.bases.arg(0))
        val y = tables.origins.root(tables.bases.arg(1))
        assertEquals(setOf(x), pts(0), "t = a.value holds x only")
        assertTrue(y !in pts(0))
    }

    private class SingleLocationUnit(val loc: RegisteredLocation) : JIRUnitResolver {
        override fun resolve(method: JIRMethod): UnitType =
            if (method.enclosingClass.declaration.location == loc) SingletonUnit else UnknownUnit

        override fun locationIsUnknown(loc: RegisteredLocation): Boolean = loc != this.loc
    }

    private companion object {
        const val INLINE = "sample.alias.DirectedInlineSample"
        const val DIRECTED = "sample.alias.DirectedAliasSample"
        const val PROBE = "probe"
    }
}
