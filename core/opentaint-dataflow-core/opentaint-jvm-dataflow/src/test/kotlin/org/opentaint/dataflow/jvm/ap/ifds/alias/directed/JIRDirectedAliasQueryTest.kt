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
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAllocInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRCallInst
import org.opentaint.ir.api.jvm.cfg.JIRClassConstant
import org.opentaint.ir.api.jvm.cfg.JIRConstant
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRLocalVar
import org.opentaint.ir.api.jvm.cfg.locals
import org.opentaint.ir.api.jvm.ext.findClass
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.ir.impl.features.usagesExt
import org.opentaint.jvm.graph.JApplicationGraphImpl
import java.util.concurrent.Callable
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue
import kotlin.time.Duration

/**
 * Tests of the facade in `DIRECTED` mode (IMPL §1.3, §1.5, §6): the query, the conversion to
 * `AliasInfo` (IMPL §6.2), the array element query (IMPL §6.3), the order of the answers, the cache
 * and the thread safety (IMPL §6.4).
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class JIRDirectedAliasQueryTest : BasicTestUtils() {

    private val languageManager by lazy { JIRLanguageManager(cp) }
    private val graph by lazy { JApplicationGraphImpl(cp, runBlocking { cp.usagesExt() }) }

    private fun facade(
        method: JIRMethod,
        params: JIRLocalAliasAnalysis.Params = JIRLocalAliasAnalysis.Params(mode = AliasAnalysisMode.DIRECTED),
    ): JIRLocalAliasAnalysis {
        val callResolver = JIRCallResolver(cp, SingleLocationUnit(method.enclosingClass.declaration.location))
        val reachability = JIRLocalVariableReachability(method, graph, languageManager)
        val cancellation = Cancellation().also { it.activate() }
        return JIRLocalAliasAnalysis(
            method.instList.first(), graph, callResolver, null, reachability, cancellation, languageManager, params,
        )
    }

    private fun method(className: String, name: String): JIRMethod =
        cp.findClass(className).declaredMethods.single { it.name == name }

    private inner class Probe(className: String, name: String, val roles: List<String>, callee: String = PROBE) {
        val method = method(className, name)
        val call: JIRCallInst = method.instList.filterIsInstance<JIRCallInst>().first { it.callExpr.method.name == callee }
        val aa = facade(method)

        fun local(role: String): AccessPathBase.LocalVar =
            AccessPathBase.LocalVar((call.callExpr.args[roles.indexOf(role)] as JIRLocalVar).index)

        private val roleOf: Map<Int, String> = roles.indices.associate { local(roles[it]).idx to roles[it] }

        fun aliases(role: String): List<AliasInfo>? = aa.findAlias(local(role), call)

        fun answer(role: String): Set<String> = assertNotNull(aliases(role)).map { show(it) }.toSortedSet()

        fun show(info: AliasInfo): String = when (info) {
            is AliasAllocInfo -> "new(${allocTarget(info.allocInst)})"
            is AliasApInfo -> when (val b = info.base) {
                is AccessPathBase.LocalVar -> roleOf[b.idx] ?: "local#${b.idx}"
                is AccessPathBase.Argument -> "arg#${b.idx}"
                is AccessPathBase.This -> "this"
                is AccessPathBase.ClassStatic -> "static"
                is AccessPathBase.Constant -> "const:${b.value}"
                else -> b.toString()
            } + info.accessors.joinToString("") { a ->
                when (a) {
                    is AliasAccessor.Field -> ".${a.fieldName}"
                    is AliasAccessor.Array -> "[*]"
                    is AliasAccessor.Static -> ":" + a.typeName.substringAfterLast('.')
                }
            }
        }

        private fun allocTarget(idx: Int): String {
            val inst = method.instList[idx] as JIRAssignInst
            val lhv = inst.lhv as JIRLocalVar
            return roleOf[lhv.index] ?: "#$idx"
        }
    }

    @Test
    fun `facade in directed mode gives the directed answers`() {
        val p = Probe(SAMPLE, "heapChainAllocs", listOf("z", "y", "x"))
        assertEquals(setOf("new(y)", "x.value", "y"), p.answer("z"))
        assertEquals(setOf("new(x)"), p.answer("x"))
        // The heap-path query reports paths only (spec §5.7).
        val heap = assertNotNull(p.aa.findHeapAlias(p.local("x"), listOf(field(BOX, "value")), p.call))
        assertEquals(setOf("y", "z"), heap.map { p.show(it) }.toSet())
    }

    @Test
    fun `findAliasAfterStatement reads the state after the statement`() {
        val p = Probe(SAMPLE, "heapChainAllocs", listOf("z", "y", "x"))
        val loadZ = p.method.instList.single { it is JIRAssignInst && (it.lhv as? JIRLocalVar)?.index == p.local("z").idx }
        assertEquals(emptyList(), p.aa.findAlias(p.local("z"), loadZ))
        val after = assertNotNull(p.aa.findAliasAfterStatement(p.local("z"), loadZ)).map { p.show(it) }.toSet()
        assertEquals(setOf("new(y)", "x.value", "y"), after)
    }

    @Test
    fun `a reported local must pass the reachability of main`() {
        val p = Probe(SAMPLE, "heapChainAllocs", listOf("z", "y", "x"))
        val analysis = JIRDirectedAliasAnalysis(
            p.method.instList.first(), graph,
            JIRCallResolver(cp, SingleLocationUnit(p.method.enclosingClass.declaration.location)),
            null, JIRLocalVariableReachability(p.method, graph, languageManager),
            Cancellation().also { it.activate() }, languageManager, JIRLocalAliasAnalysis.Params(),
        )
        val result = assertNotNull(analysis.compute())
        val y = p.local("y")
        val stmt = p.call.location.index
        val all = JIRAliasAnswers(result, { _, _ -> true }, maxAccessors = 6)
        assertEquals(setOf("new(y)", "x.value", "y"), assertNotNull(all.findAlias(p.local("z").idx, stmt, false)).map { p.show(it) }.toSet())
        val withoutY = JIRAliasAnswers(result, { base, idx -> base != y || idx != stmt }, maxAccessors = 6)
        assertEquals(setOf("new(y)", "x.value"), assertNotNull(withoutY.findAlias(p.local("z").idx, stmt, false)).map { p.show(it) }.toSet())
    }

    @Test
    fun `static holder path has the class static base and the static type name of main`() {
        val p = Probe(NESTED_STATICS, "staticWriteThenRead", listOf("t", "v"))
        val info = assertNotNull(p.aliases("t")).single() as AliasApInfo
        assertEquals(AccessPathBase.ClassStatic, info.base)
        val dsu = facade(p.method, JIRLocalAliasAnalysis.Params(mode = AliasAnalysisMode.DSU))
        val dsuInfo = assertNotNull(dsu.findAlias(p.local("t"), p.call)).filterIsInstance<AliasApInfo>()
            .single { it.base == AccessPathBase.ClassStatic }
        assertEquals(dsuInfo.accessors, info.accessors)
        assertEquals(
            listOf(
                AliasAccessor.Static("sample.alias.DirectedAliasSample.NestedStatics.NestedStatics\$Inner"),
                AliasAccessor.Field("$NESTED_STATICS\$Inner", "innerStatic", OBJECT),
            ),
            info.accessors,
        )
        // The static write is ignored: v aliases only its own allocation.
        assertEquals(setOf("new(v)"), p.answer("v"))
    }

    @Test
    fun `vararg string constants are the element aliases without the element path`() {
        val p = Probe(SAMPLE, "varargStringConstants", listOf("values"), callee = VARARGS)
        val elements = assertNotNull(p.aa.findArrayElementAliases(p.local("values"), p.call))
        assertEquals(
            listOf(
                AliasApInfo(AccessPathBase.Constant("java.lang.String", "a"), emptyList()),
                AliasApInfo(AccessPathBase.Constant("java.lang.String", "b"), emptyList()),
            ),
            elements,
        )
    }

    @Test
    fun `vararg element constants of boxes are the valueOf statements`() {
        val p = Probe(SAMPLE, "varargBoxedConstants", listOf("values"), callee = VARARGS)
        val elements = assertNotNull(p.aa.findArrayElementAliases(p.local("values"), p.call))
        assertTrue(elements.all { it is AliasAllocInfo }, elements.toString())
        val calls = elements.map { p.method.instList[(it as AliasAllocInfo).allocInst].callExpr.toString() }.toSet()
        assertEquals(setOf("java.lang.Boolean.valueOf(1)", "java.lang.Integer.valueOf(1)"), calls)

        val dsu = facade(p.method, JIRLocalAliasAnalysis.Params(mode = AliasAnalysisMode.DSU))
        val dsuCalls = assertNotNull(dsu.findArrayElementAliases(p.local("values"), p.call))
            .filterIsInstance<AliasAllocInfo>()
            .map { p.method.instList[it.allocInst].callExpr.toString() }.toSet()
        assertEquals(dsuCalls, calls)
    }

    @Test
    fun `a box of a value and a class constant are allocation items`() {
        val box = Probe(SAMPLE, "boxOfValue", listOf("a", "b"))
        val a = assertNotNull(box.aliases("a")).single() as AliasAllocInfo
        val aCall = box.method.instList[a.allocInst].callExpr
        assertEquals("valueOf", aCall?.method?.name)
        assertTrue(aCall!!.args.single() !is JIRConstant)
        val b = assertNotNull(box.aliases("b")).single() as AliasAllocInfo
        val bCall = box.method.instList[b.allocInst].callExpr
        assertEquals("valueOf", bCall?.method?.name)
        assertTrue(bCall!!.args.single() is JIRConstant)

        val cls = Probe(SAMPLE, "classConstant", listOf("c"))
        val c = assertNotNull(cls.aliases("c")).single() as AliasAllocInfo
        assertTrue((cls.method.instList[c.allocInst] as JIRAssignInst).rhv is JIRClassConstant)
    }

    @Test
    fun `null and fresh values give no item`() {
        val p = Probe(SAMPLE, "nullAndFresh", listOf("n", "r"))
        assertEquals(emptyList(), p.aliases("n"))
        assertEquals(emptyList(), p.aliases("r"))
    }

    @Test
    fun `a local that the analysis does not know gives no answer`() {
        val p = Probe(SAMPLE, "heapChainAllocs", listOf("z", "y", "x"))
        assertNull(p.aa.findAlias(AccessPathBase.LocalVar(500), p.call))
        assertNull(p.aa.findAliasAfterStatement(AccessPathBase.LocalVar(500), p.call))
        assertNull(p.aa.findArrayElementAliases(AccessPathBase.LocalVar(500), p.call))
    }

    @Test
    fun `the facade gives no answer when the alias analysis is off or out of time`() {
        val m = method(SAMPLE, "heapChainAllocs")
        val call = m.instList.filterIsInstance<JIRCallInst>().first { it.callExpr.method.name == PROBE }
        val z = AccessPathBase.LocalVar((call.callExpr.args[0] as JIRLocalVar).index)
        val off = facade(m, JIRLocalAliasAnalysis.Params(useAliasAnalysis = false, mode = AliasAnalysisMode.DIRECTED))
        assertNull(off.findAlias(z, call))
        assertNull(off.findAliasAfterStatement(z, call))
        assertNull(off.findArrayElementAliases(z, call))
        val timeOut = facade(
            m, JIRLocalAliasAnalysis.Params(aliasAnalysisTimeLimit = Duration.ZERO, mode = AliasAnalysisMode.DIRECTED),
        )
        assertNull(timeOut.findAlias(z, call))
        assertNull(timeOut.findHeapAlias(z, listOf(field(BOX, "value")), call))
    }

    @Test
    fun `answers are sorted with one fixed order and have no duplicates`() {
        val p = Probe(SAMPLE, "manyLocals", listOf("x", "y", "t", "u", "s"))
        for (role in p.roles) {
            val answer = assertNotNull(p.aliases(role))
            assertEquals(answer.sortedWith(AliasInfoOrder), answer, role)
            assertEquals(answer.distinct(), answer, role)
        }
        assertEquals(setOf("const:s"), p.answer("s"))

        val field = field(BOX, "value")
        val expected = listOf(
            AliasApInfo(AccessPathBase.This, emptyList()),
            AliasApInfo(AccessPathBase.Argument(0), emptyList()),
            AliasApInfo(AccessPathBase.Argument(0), listOf(field)),
            AliasApInfo(AccessPathBase.Argument(1), emptyList()),
            AliasApInfo(AccessPathBase.LocalVar(0), listOf(AliasAccessor.Array)),
            AliasApInfo(AccessPathBase.LocalVar(2), emptyList()),
            AliasApInfo(AccessPathBase.ClassStatic, listOf(AliasAccessor.Static("A"), field)),
            AliasApInfo(AccessPathBase.Constant("java.lang.String", "a"), emptyList()),
            AliasAllocInfo(1),
            AliasAllocInfo(4),
        )
        assertEquals(expected, expected.reversed().sortedWith(AliasInfoOrder))
        assertEquals(expected, expected.shuffled(kotlin.random.Random(7)).sortedWith(AliasInfoOrder))
    }

    @Test
    fun `answers do not depend on query order`() {
        for ((className, name) in ORDER_METHODS) {
            val m = method(className, name)
            val queries = allQueries(m)
            val forward = facade(m)
            val backward = facade(m)
            val first = queries.associateWith { forward.answer(it) }
            val second = queries.reversed().associateWith { backward.answer(it) }
            for (q in queries) assertEquals(first[q], second[q], "$name $q")
        }
    }

    @Test
    fun `concurrent queries give equal answers`() {
        val pool = Executors.newFixedThreadPool(8)
        try {
            for ((className, name) in ORDER_METHODS) {
                val m = method(className, name)
                val queries = allQueries(m)
                val expected = facade(m).let { aa -> queries.associateWith { aa.answer(it) } }
                val shared = facade(m)
                val tasks = (0 until 8).map { seed ->
                    Callable { queries.shuffled(kotlin.random.Random(seed)).associateWith { shared.answer(it) } }
                }
                for (result in pool.invokeAll(tasks).map { it.get(60, TimeUnit.SECONDS) }) {
                    for (q in queries) assertEquals(expected[q], result[q], "$name $q")
                }
            }
        } finally {
            pool.shutdownNow()
        }
    }

    /** A query: [kind] 0 is `findAlias`, 1 is `findAliasAfterStatement`, 2 is `findArrayElementAliases`. */
    private data class Query(val kind: Int, val local: Int, val inst: JIRInst)

    private fun allQueries(m: JIRMethod): List<Query> {
        val locals = m.instList.flatMap { it.locals }.filterIsInstance<JIRLocalVar>().map { it.index }.distinct()
        return m.instList.flatMap { inst ->
            locals.flatMap { l -> (0..2).map { Query(it, l, inst) } }
        }
    }

    private fun JIRLocalAliasAnalysis.answer(q: Query): List<AliasInfo>? {
        val base = AccessPathBase.LocalVar(q.local)
        return when (q.kind) {
            0 -> findAlias(base, q.inst)
            1 -> findAliasAfterStatement(base, q.inst)
            else -> findArrayElementAliases(base, q.inst)
        }
    }

    private fun field(className: String, name: String): AliasAccessor.Field = AliasAccessor.Field(className, name, OBJECT)

    private class SingleLocationUnit(val loc: RegisteredLocation) : JIRUnitResolver {
        override fun resolve(method: JIRMethod): UnitType =
            if (method.enclosingClass.declaration.location == loc) SingletonUnit else UnknownUnit

        override fun locationIsUnknown(loc: RegisteredLocation): Boolean = loc != this.loc
    }

    private companion object {
        const val SAMPLE = "sample.alias.DirectedAliasSample"
        const val BOX = "$SAMPLE\$Box"
        const val NESTED_STATICS = "$SAMPLE\$NestedStatics"
        const val OBJECT = "java.lang.Object"
        const val PROBE = "probe"
        const val VARARGS = "varargs"

        val ORDER_METHODS = listOf(
            SAMPLE to "manyLocals",
            SAMPLE to "listWalkWithSecond",
            SAMPLE to "fieldWriteThroughJoinArgs",
            SAMPLE to "catchAfterThrowingCall",
            SAMPLE to "varargBoxedConstants",
        )
    }
}
