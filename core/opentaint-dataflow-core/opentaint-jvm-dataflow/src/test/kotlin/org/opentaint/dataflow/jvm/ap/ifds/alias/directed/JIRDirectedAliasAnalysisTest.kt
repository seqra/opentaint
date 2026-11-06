package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.jvm.BasicTestUtils
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.alias.InstEvalContext
import org.opentaint.dataflow.jvm.ap.ifds.alias.RefValue
import org.opentaint.dataflow.jvm.ap.ifds.alias.Stmt
import org.opentaint.dataflow.jvm.ap.ifds.alias.Value
import org.opentaint.dataflow.jvm.ap.ifds.alias.evalInst
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRCallInst
import org.opentaint.ir.api.jvm.cfg.JIRCatchInst
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRIfInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRLocalVar
import org.opentaint.ir.api.jvm.cfg.JIRNullConstant
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRStringConstant
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.ir.api.jvm.ext.findClass
import org.opentaint.ir.impl.features.usagesExt
import org.opentaint.jvm.graph.JApplicationGraphImpl
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

/**
 * Tests of the JIR adapter of the directed engine: the alias CFG of a JIR method, the lowering of
 * IMPL §4.1, and the fixpoint with the post-fixpoint check on the JIR samples.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class JIRDirectedAliasAnalysisTest : BasicTestUtils() {

    private val languageManager by lazy { JIRLanguageManager(cp) }
    private val graph by lazy { JApplicationGraphImpl(cp, runBlocking { cp.usagesExt() }) }

    private fun analyze(method: JIRMethod): DirectedAliasResult {
        val ep = method.instList.first()
        val callResolver = JIRCallResolver(cp, SingleLocationUnit(method.enclosingClass.declaration.location))
        val reachability = JIRLocalVariableReachability(method, graph, languageManager)
        val cancellation = Cancellation().also { it.activate() }
        val analysis = JIRDirectedAliasAnalysis(
            ep, graph, callResolver, null, reachability, cancellation, languageManager,
            JIRLocalAliasAnalysis.Params(), verifyPostFix = true,
        )
        return assertNotNull(analysis.compute(), "no result for ${method.name}")
    }

    private fun method(className: String, name: String): JIRMethod =
        cp.findClass(className).declaredMethods.single { it.name == name }

    private class Analyzed(val method: JIRMethod, val result: DirectedAliasResult) {
        val tables get() = result.tables

        fun inst(predicate: (JIRInst) -> Boolean): JIRInst = method.instList.single(predicate)

        fun instr(inst: JIRInst): AliasInstr = result.cfg.instr(inst.location.index)

        fun probe(): JIRCallInst = method.instList.filterIsInstance<JIRCallInst>().first { it.callExpr.method.name == "probe" }

        fun varOf(local: JIRLocalVar): VarId = tables.vars.local(local.index)

        fun probeArg(i: Int): VarId = varOf(probe().callExpr.args[i] as JIRLocalVar)

        fun pts(before: JIRInst, v: VarId): Set<OriginId> {
            val st = assertNotNull(result.statesBefore[before.location.index])
            return tables.nodes.members(st.varNode(v)).toSet()
        }

        fun argO(i: Int): OriginId = tables.origins.root(tables.bases.arg(i))

        fun cellOf(field: String): CellId = tables.cells.field("$SAMPLE\$Box", field, "java.lang.Object")
    }

    private fun analyzed(className: String, name: String): Analyzed {
        val m = method(className, name)
        return Analyzed(m, analyze(m))
    }

    @Test
    fun `post-fixpoint check passes on each method of the directed alias sample`() {
        val classes = listOf(
            SAMPLE, "$SAMPLE\$Box", "$SAMPLE\$Holder", "$SAMPLE\$FinalBox", "$SAMPLE\$CtorLoop",
            "$SAMPLE\$CtorJoin", "$SAMPLE\$ThisWrites", "$SAMPLE\$GenericStatics", "$SAMPLE\$NestedStatics",
            "$SAMPLE\$NestedStatics\$Inner", "$SAMPLE\$Counter",
        )
        var count = 0
        for (className in classes) {
            for (m in cp.findClass(className).declaredMethods) {
                if (m.instList.size == 0) continue
                val result = analyze(m)
                assertTrue(result.tables.nodes.isFrozen)
                count++
            }
        }
        assertTrue(count > 60, "only $count methods")
    }

    @Test
    fun `handler of a JIR catch has exceptional edges from its throwers and no normal edge`() {
        val a = analyzed(SAMPLE, "catchAfterThrowingCall")
        val catch = a.inst { it is JIRCatchInst } as JIRCatchInst
        val call = a.inst { it is JIRCallInst && it.callExpr.method.name == "mayThrow" }
        val h = catch.location.index
        assertEquals(catch.throwers.map { it.index }.sorted(), a.result.cfg.throwers(h).toList().sorted())
        assertTrue(call.location.index in a.result.cfg.throwers(h))
        assertEquals(emptyList(), a.result.cfg.normalPredecessors(h).toList())
        val e = a.varOf(catch.throwable as JIRLocalVar)
        assertEquals(AliasInstr.Assign(e, AliasValue.Fresh(a.tables.sites.site(h))), a.instr(catch))
    }

    @Test
    fun `handler gets the state before a throwing call in a JIR method`() {
        val a = analyzed(SAMPLE, "catchAfterThrowingCall")
        val probe = a.probe()
        // The provisional `<init>` call puts REACHED_ALL into Etree, so `x.value = v` is a weak store:
        // t gets the stored value and the default child of the new object.
        val x = a.pts(probe, a.probeArg(2)).single()
        val child = a.tables.nodes.members(a.tables.origins.defaultNode(x, a.cellOf("value"))).toSet()
        assertEquals(child + a.argO(0), a.pts(probe, a.probeArg(0)))
        assertEquals(setOf(a.argO(0)), a.pts(probe, a.probeArg(1)))
    }

    @Test
    fun `kill keeps a JIR local that a handler reads`() {
        val a = analyzed(SAMPLE, "handlerReadsOverwrittenLocal")
        val store = a.inst { it is JIRAssignInst && it.lhv is JIRFieldRef }
        val ref = (store as JIRAssignInst).lhv as JIRFieldRef
        val x = a.varOf(ref.instance as JIRLocalVar)
        val y = a.varOf(store.rhv as JIRLocalVar)
        val common = a.pts(store, x) intersect a.pts(store, y)
        assertTrue(common.any { a.tables.origins.isAllocNew(it) }, "x and y must share the new object")
    }

    @Test
    fun `loop at the first instruction gets a JIR goto and a loop head after it`() {
        val a = analyzed(SAMPLE, "loopAtFirstInstruction")
        val wto = a.result.cfg.wto
        assertEquals(WtoComponent.Vertex(0), wto.first())
        assertEquals(1, assertIs<WtoComponent.Loop>(wto[1]).head)
    }

    @Test
    fun `a local that only a branch reads stays live at the branch`() {
        val a = analyzed(SAMPLE, "nullCheckOnly")
        val branch = a.inst { it is JIRIfInst }
        val x = a.method.instList.firstNotNullOf { ((it as? JIRAssignInst)?.lhv as? JIRLocalVar) }
        assertEquals(1, a.pts(branch, a.varOf(x)).size)
    }

    @Test
    fun `box of a constant is a shared constant and box of a value is a box origin`() {
        val boxed = analyzed(SAMPLE, "varargBoxedConstants")
        val consts = boxed.method.instList.filter { it.callExpr?.method?.name == "valueOf" }.map { inst ->
            val instr = assertIs<AliasInstr.Assign>(boxed.instr(inst))
            boxed.tables.bases.key(assertIs<AliasValue.Const>(instr.value).base)
        }
        assertEquals(
            setOf(BaseKey.Const("java.lang.Integer", "1"), BaseKey.Const("java.lang.Boolean", "1")),
            consts.toSet(),
        )

        val value = analyzed(SAMPLE, "boxOfValue")
        val calls = value.method.instList.filter { it.callExpr?.method?.name == "valueOf" }
        val values = calls.map { assertIs<AliasInstr.Assign>(value.instr(it)).value }
        assertEquals(AliasValue.Box(value.tables.sites.site(calls[0].location.index)), values[0])
        assertEquals(
            BaseKey.Const("java.lang.Integer", "1"),
            value.tables.bases.key(assertIs<AliasValue.Const>(values[1]).base),
        )
    }

    @Test
    fun `null string and class constants are lowered by the assign rules`() {
        val nul = analyzed(SAMPLE, "loopSiteStrongUpdateAfterNullPrev")
        val nullAssign = nul.inst { it is JIRAssignInst && it.rhv is JIRNullConstant }
        assertEquals(
            AliasValue.Null(nul.tables.sites.site(nullAssign.location.index)),
            assertIs<AliasInstr.Assign>(nul.instr(nullAssign)).value,
        )

        val str = analyzed(SAMPLE, "varargStringConstants")
        val stored = str.method.instList.map { str.instr(it) }.filterIsInstance<AliasInstr.ArrayStore>()
        assertEquals(
            setOf(BaseKey.Const(STRING_TYPE, "a"), BaseKey.Const(STRING_TYPE, "b")),
            stored.map { str.tables.bases.key(assertIs<AliasValue.Const>(it.value).base) }.toSet(),
        )

        val cls = analyzed(SAMPLE, "classConstant")
        val classes = cls.method.instList.map { cls.instr(it) }.filterIsInstance<AliasInstr.Assign>()
            .mapNotNull { (it.value as? AliasValue.Const)?.let { c -> cls.tables.bases.key(c.base) } }
        assertEquals(listOf(BaseKey.Const(CLASS_TYPE, "java.lang.String")), classes)
    }

    @Test
    fun `static read is keyed by the binary class name and records the type name`() {
        val a = analyzed("$SAMPLE\$GenericStatics", "staticWriteThenRead")
        val instrs = a.method.instList.map { a.instr(it) }
        assertTrue(AliasInstr.StaticWrite in instrs)
        val read = instrs.filterIsInstance<AliasInstr.StaticRead>().single()
        assertEquals(BaseKey.Static("$SAMPLE\$GenericStatics"), a.tables.bases.key(read.staticBase))
        assertEquals("$SAMPLE.GenericStatics<T>", a.tables.bases.staticTypeName(read.staticBase))
        assertEquals(
            CellTable.FieldKey("$SAMPLE\$GenericStatics", "genericStatic", "java.lang.Object"),
            a.tables.cells.fieldKey(read.cell),
        )
    }

    @Test
    fun `a primitive value is never stored`() {
        val a = analyzed(SAMPLE, "primitiveStore")
        val store = a.inst { it is JIRAssignInst && it.lhv is JIRFieldRef }
        assertEquals(AliasInstr.Nop, a.instr(store))
    }

    @Test
    fun `a call is an unresolved call with the receiver first`() {
        val a = analyzed(SAMPLE, "loadThenJdkCallArg")
        val call = a.inst { it.callExpr?.method?.name == "append" }
        val instr = assertIs<AliasInstr.UnresolvedCall>(a.instr(call))
        assertEquals(a.tables.sites.site(call.location.index), instr.site)
        assertEquals(listOf<AliasValue>(AliasValue.Arg(1), AliasValue.Arg(0)), instr.args)
    }

    @Test
    fun `return of a constant carries the constant in the builder`() {
        val ctx = object : InstEvalContext {
            override fun createThis(isOuter: Boolean): Value = RefValue.This(isOuter)
            override fun createArg(idx: Int): Value = RefValue.Arg(idx)
            override fun createLocal(idx: Int): RefValue.Local = RefValue.Local(idx, ContextInfo.rootContext)
        }

        val string = method(SAMPLE, "returnString").instList.filterIsInstance<JIRReturnInst>().single()
        val s = assertIs<Stmt.Return>(ctx.evalInst(string))
        assertNull(s.value)
        assertEquals("s", assertIs<JIRStringConstant>(assertNotNull(s.constant).expr).value)

        val nul = method(SAMPLE, "returnNull").instList.filterIsInstance<JIRReturnInst>().single()
        val n = assertIs<Stmt.Return>(ctx.evalInst(nul))
        assertNull(n.value)
        assertIs<JIRNullConstant>(assertNotNull(n.constant).expr)

        val arg = method(SAMPLE, "choose").instList.filterIsInstance<JIRReturnInst>().single()
        val r = assertIs<Stmt.Return>(ctx.evalInst(arg))
        assertEquals(RefValue.Arg(0), r.value)
        assertNull(r.constant)
    }

    @Test
    fun `return of a constant is lowered with the assign rules`() {
        val a = analyzed(SAMPLE, "returnString")
        val ret = a.inst { it is JIRReturnInst }
        val value = assertIs<AliasValue.Const>(assertIs<AliasInstr.Return>(a.instr(ret)).value)
        assertEquals(BaseKey.Const(STRING_TYPE, "s"), a.tables.bases.key(value.base))

        val n = analyzed(SAMPLE, "returnNull")
        val nret = n.inst { it is JIRReturnInst }
        assertEquals(
            AliasInstr.Return(AliasValue.Null(n.tables.sites.site(nret.location.index))),
            n.instr(nret),
        )
    }

    private class SingleLocationUnit(val loc: RegisteredLocation) : JIRUnitResolver {
        override fun resolve(method: JIRMethod): UnitType =
            if (method.enclosingClass.declaration.location == loc) SingletonUnit else UnknownUnit

        override fun locationIsUnknown(loc: RegisteredLocation): Boolean = loc != this.loc
    }

    private companion object {
        const val SAMPLE = "sample.alias.DirectedAliasSample"
    }
}
