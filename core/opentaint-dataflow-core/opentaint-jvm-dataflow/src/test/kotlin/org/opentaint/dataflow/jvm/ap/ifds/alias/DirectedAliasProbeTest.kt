package org.opentaint.dataflow.jvm.ap.ifds.alias

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.jvm.Argument
import org.opentaint.dataflow.configuration.jvm.CopyAllMarks
import org.opentaint.dataflow.configuration.jvm.IsConstant
import org.opentaint.dataflow.configuration.jvm.Result
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.jvm.BasicTestUtils
import org.opentaint.dataflow.jvm.ap.ifds.AliasAnalysisMode
import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.checkDirectedPostFix
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAllocInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.JIRField
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.cfg.JIRArgument
import org.opentaint.ir.api.jvm.cfg.JIRArrayAccess
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRCallInst
import org.opentaint.ir.api.jvm.cfg.JIRCastExpr
import org.opentaint.ir.api.jvm.cfg.JIRCatchInst
import org.opentaint.ir.api.jvm.cfg.JIRExpr
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRGotoInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRLocalVar
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.ir.impl.features.usagesExt
import org.opentaint.jvm.graph.JApplicationGraphImpl
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNull
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class DirectedAliasProbeTest : BasicTestUtils() {
    private class ProbeRules(private val passThrough: Map<String, List<CopyAllMarks>>) : TaintRulesProvider {
        override fun entryPointRulesForMethod(
            method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
        ): Iterable<TaintEntryPointSource> = emptyList()

        override fun sourceRulesForMethod(
            method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
        ): Iterable<TaintMethodSource> = emptyList()

        override fun exitSourceRulesForMethod(
            method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
        ): Iterable<TaintMethodExitSource> = emptyList()

        override fun sinkRulesForMethod(
            method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
        ): Iterable<TaintMethodSink> = emptyList()

        override fun sinkRulesForMethodEntry(
            method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
        ): Iterable<TaintMethodEntrySink> = emptyList()

        override fun sinkRulesForMethodExit(
            method: CommonMethod,
            statement: CommonInst,
            fact: FactAp?,
            initialFacts: Set<InitialFactAp>?,
            allRelevant: Boolean
        ): Iterable<TaintMethodExitSink> = emptyList()

        override fun passTroughRulesForMethod(
            method: CommonMethod, statement: CommonInst?, fact: FactAp?, allRelevant: Boolean
        ): Iterable<TaintPassThrough> {
            val actions = passThrough[method.name] ?: return emptyList()
            return listOf(TaintPassThrough(method, CommonCondition.Atom(IsConstant(Result)), actions, info = null))
        }

        override fun cleanerRulesForMethod(
            method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
        ): Iterable<TaintCleaner> = emptyList()

        override fun sourceRulesForStaticField(
            field: JIRField, statement: CommonInst, fact: FactAp?, allRelevant: Boolean
        ): Iterable<TaintStaticFieldSource> = emptyList()

        override fun selectRules(ruleIds: Set<String>) = Unit
    }

    private val noRules = ProbeRules(emptyMap())

    private val manager by lazy { JIRAnalysisManager(cp, RefManager(), noRules) }

    @Test
    fun `today join of two allocations makes x alias y`() {
        val p = probeAt(SAMPLE, "joinOfAllocs", "x", "y", "a")
        assertEquals(setOf("a", "new(x)", "new(y)", "y"), p.answer("x"))
        assertEquals(setOf("a", "new(x)", "new(y)", "x"), p.answer("y"))
        assertEquals(setOf("new(x)", "new(y)", "x", "y"), p.answer("a"))
    }

    @Test
    fun `today join of two arguments makes x alias y`() {
        val p = probeAt(SAMPLE, "joinOfArgs", "x", "y", "a")
        assertEquals(setOf("a", "arg:px", "arg:py", "y"), p.answer("x"))
        assertEquals(setOf("a", "arg:px", "arg:py", "x"), p.answer("y"))
        assertEquals(setOf("arg:px", "arg:py", "x", "y"), p.answer("a"))
    }

    @Test
    fun `today field write through a join of allocations keeps x and y merged after the join variable is reassigned`() {
        val p = probeAt(SAMPLE, "fieldWriteThroughJoinAllocs", "z", "x", "y", "xv", "yv")
        assertEquals(setOf("new(z)", "x.value", "xv", "y.value", "yv"), p.answer("z"))
        assertEquals(setOf("new(x)", "new(y)", "y"), p.answer("x"))
        assertEquals(setOf("new(x)", "new(y)", "x"), p.answer("y"))
        assertEquals(setOf("new(z)", "x.value", "y.value", "yv", "z"), p.answer("xv"))
        assertEquals(setOf("new(z)", "x.value", "xv", "y.value", "z"), p.answer("yv"))
        assertEquals(setOf("new(z)", "xv", "yv", "z"), p.heapAnswer("x", BOX, "value"))
        assertEquals(setOf("new(z)", "xv", "yv", "z"), p.heapAnswer("y", BOX, "value"))
    }

    @Test
    fun `today field write through a join of arguments keeps x and y merged after the join variable is reassigned`() {
        val p = probeAt(SAMPLE, "fieldWriteThroughJoinArgs", "z", "x", "y", "xv", "yv")
        assertEquals(setOf("arg:px.value", "arg:py.value", "arg:pz", "x.value", "xv", "y.value", "yv"), p.answer("z"))
        assertEquals(setOf("arg:px", "arg:py", "y"), p.answer("x"))
        assertEquals(setOf("arg:px", "arg:py", "x"), p.answer("y"))
        assertEquals(setOf("arg:px.value", "arg:py.value", "arg:pz", "x.value", "y.value", "yv", "z"), p.answer("xv"))
        assertEquals(setOf("arg:pz", "xv", "yv", "z"), p.heapAnswer("x", BOX, "value"))
        assertEquals(setOf("arg:pz", "xv", "yv", "z"), p.heapAnswer("y", BOX, "value"))
    }

    @Test
    fun `today store through a join of allocations is visible through the other variable`() {
        val p = probeAt(SAMPLE, "storeThroughJoinLoadThroughOtherAllocs", "t", "z")
        assertEquals(setOf("new(z)", "z"), p.answer("t"))
        assertEquals(setOf("new(z)", "t"), p.answer("z"))
    }

    @Test
    fun `today store through a join of arguments is visible through both argument paths`() {
        val p = probeAt(SAMPLE, "storeThroughJoinLoadThroughOtherArgs", "t", "z")
        assertEquals(setOf("arg:px.value", "arg:py.value", "arg:pz", "z"), p.answer("t"))
        assertEquals(setOf("arg:px.value", "arg:py.value", "arg:pz", "t"), p.answer("z"))
    }

    @Test
    fun `today correlated branches make a alias b`() {
        val p = probeAt(SAMPLE, "correlatedBranches", "a", "b")
        assertEquals(setOf("b", "new(a#6)", "new(b#7)"), p.answer("a"))
        assertEquals(setOf("a", "new(a#6)", "new(b#7)"), p.answer("b"))
    }

    @Test
    fun `today loop reassignment makes a alias b`() {
        val p = probeAt(SAMPLE, "loopReassign", "a", "b", "cur")
        assertEquals(setOf("b", "cur", "new(a)", "new(b)"), p.answer("a"))
        assertEquals(setOf("a", "cur", "new(a)", "new(b)"), p.answer("b"))
        assertEquals(setOf("a", "b", "new(a)", "new(b)"), p.answer("cur"))
    }

    @Test
    fun `today heap chain load aliases the stored value`() {
        val p = probeAt(SAMPLE, "heapChainAllocs", "z", "y", "x")
        assertEquals(setOf("new(y)", "x.value", "y"), p.answer("z"))
        assertEquals(setOf("new(y)", "x.value", "z"), p.answer("y"))
        assertEquals(setOf("new(x)"), p.answer("x"))
        assertEquals(setOf("new(y)", "y", "z"), p.heapAnswer("x", BOX, "value"))
    }

    @Test
    fun `today load through a join of two arguments makes p value alias q value`() {
        val p = probeAt(SAMPLE, "loadThroughJoinOfArgs", "t", "pv")
        assertEquals(setOf("arg:p.value", "arg:q.value", "pv"), p.answer("t"))
        assertEquals(setOf("arg:p.value", "arg:q.value", "t"), p.answer("pv"))
    }

    @Test
    fun `today pass-through models of two arguments into one result make x alias y`() {
        val rules = ProbeRules(
            mapOf("choose" to listOf(CopyAllMarks(Argument(0), Result), CopyAllMarks(Argument(1), Result)))
        )
        val p = probeAt(SAMPLE, "passThroughOfTwoArgs", "x", "y", "r", rules = rules)
        assertEquals(setOf("arg:px", "arg:py", "r", "y"), p.answer("x"))
        assertEquals(setOf("arg:px", "arg:py", "r", "x"), p.answer("y"))
        assertEquals(setOf("arg:px", "arg:py", "x", "y"), p.answer("r"))
    }

    @Test
    fun `today without pass-through models the call result is unrelated to the arguments`() {
        val p = probeAt(SAMPLE, "passThroughOfTwoArgs", "x", "y", "r")
        assertEquals(setOf("arg:px"), p.answer("x"))
        assertEquals(setOf("arg:py"), p.answer("y"))
        assertNull(p.answer("r"))
    }

    @Test
    fun `today strong update on a loop allocation site drops the previous object field after an invalidated load`() {
        val p = probeAt(SAMPLE, "loopSiteStrongUpdateAfterInvalidatedLoad", "seen", "prev", "cur")
        assertEquals(setOf("%4#4", "arg:pa"), p.answer("seen"))
        assertEquals(setOf("cur", "new(cur)"), p.answer("prev"))
        assertEquals(setOf("%5#5", "arg:pw"), p.heapAnswer("prev", BOX, "value"))
    }

    @Test
    fun `today strong update on a loop allocation site in a constructor drops this value and the previous object field`() {
        val p = probeAt(CTOR_LOOP, "<init>", "seen", "prev", "cur")
        assertEquals(setOf("%3#3", "arg:pa"), p.answer("seen"))
        assertEquals(setOf("cur", "new(cur)", "this"), p.answer("prev"))
        assertEquals(setOf("%4#4", "arg:pw"), p.heapAnswer("prev", BOX, "value"))
    }

    @Test
    fun `today strong update on a join of constructor this and an allocation drops this value`() {
        val p = probeAt(CTOR_JOIN, "<init>", "seen", "n")
        assertEquals(setOf("arg:pa"), p.answer("seen"))
        assertEquals(setOf("new(n#3)", "this"), p.answer("n"))
    }

    @Test
    fun `today strong update on a join of an invalidated load and an allocation drops the load field`() {
        val p = probeAt(SAMPLE, "joinOfInvalidatedLoadAndAlloc", "seen", "n", "p")
        assertEquals(setOf("arg:pa"), p.answer("seen"))
        assertEquals(setOf("new(n#5)", "p"), p.answer("n"))
        assertEquals(setOf("arg:pw"), p.heapAnswer("p", BOX, "value"))
    }

    @Test
    fun `today allocated predecessor blocks the loop strong update`() {
        val p = probeAt(SAMPLE, "loopSiteStrongUpdateAfterAllocatedPrev", "seen", "prev", "cur")
        assertEquals(setOf("%3#3", "%4#4", "arg:pa", "arg:pw", "cur.value", "prev.value"), p.answer("seen"))
        assertEquals(setOf("cur", "new(cur)", "new(prev#1)"), p.answer("prev"))
    }

    @Test
    fun `today null predecessor blocks the loop strong update`() {
        val p = probeAt(SAMPLE, "loopSiteStrongUpdateAfterNullPrev", "seen", "prev", "cur")
        assertEquals(setOf("%2#2", "%3#3", "arg:pa", "arg:pw", "cur.value", "prev.value"), p.answer("seen"))
        assertEquals(setOf("cur", "new(cur)"), p.answer("prev"))
    }

    @Test
    fun `today argument predecessor blocks the loop strong update`() {
        val p = probeAt(SAMPLE, "loopSiteStrongUpdateAfterArgPrev", "seen", "prev", "cur")
        assertEquals(
            setOf("%3#3", "%4#4", "arg:p.value", "arg:pa", "arg:pw", "cur.value", "prev.value"),
            p.answer("seen")
        )
        assertEquals(setOf("arg:p", "cur", "new(cur)"), p.answer("prev"))
    }

    @Test
    fun `today call return predecessor blocks the loop strong update`() {
        val p = probeAt(SAMPLE, "loopSiteStrongUpdateAfterCallReturnPrev", "seen", "prev", "cur")
        assertEquals(setOf("%3#3", "%4#4", "arg:pa", "arg:pw", "cur.value", "prev.value"), p.answer("seen"))
        assertEquals(setOf("cur", "new(cur)"), p.answer("prev"))
    }

    @Test
    fun `today unknown call on the argument removes the loaded field alias`() {
        val p = probeAt(SAMPLE, "loadThenUnknownCallArg", "w")
        assertNull(p.answer("w"))
    }

    @Test
    fun `today unknown call on the local allocation removes the loaded field alias`() {
        val p = probeAt(SAMPLE, "loadThenUnknownCallLocal", "w", "x")
        assertEquals(setOf("arg:v"), p.answer("w"))
        assertEquals(setOf("new(x)"), p.answer("x"))
    }

    @Test
    fun `today unknown call on an unrelated argument keeps the field alias of an argument used directly`() {
        val p = probeAt(SAMPLE, "loadThenUnrelatedCallArg", "w")
        assertEquals(setOf("arg:x.value"), p.answer("w"))
    }

    @Test
    fun `today unknown call on an unrelated argument removes the field alias of an argument copied to a local`() {
        val p = probeAt(SAMPLE, "loadThenUnrelatedCallCopiedArg", "w", "x")
        assertEquals(emptySet<String>(), p.answer("w"))
        assertEquals(setOf("arg:px"), p.answer("x"))
    }

    @Test
    fun `today unknown call on the argument removes the loaded final field alias`() {
        val p = probeAt(SAMPLE, "loadThenUnknownCallFinalArg", "w")
        assertNull(p.answer("w"))
    }

    @Test
    fun `today unknown call on the local allocation keeps the loaded final field alias`() {
        val p = probeAt(SAMPLE, "loadThenUnknownCallFinalLocal", "w", "x")
        assertEquals(setOf("x.value"), p.answer("w"))
        assertEquals(setOf("new(x)"), p.answer("x"))
    }

    @Test
    fun `today jdk call on the argument removes the loaded field alias`() {
        val p = probeAt(SAMPLE, "loadThenJdkCallArg", "w")
        assertNull(p.answer("w"))
    }

    @Test
    fun `today static field write is ignored so the static read does not alias the written value`() {
        val p = probeAt(SAMPLE, "staticWriteThenRead", "t", "v")
        assertEquals(setOf("static:DirectedAliasSample.staticField"), p.answer("t"))
        assertEquals(setOf("new(v)"), p.answer("v"))
    }

    @Test
    fun `today this field write in a constructor is a strong update`() {
        val p = probeAt(THIS_WRITES, "<init>", "t", "v1", "v2")
        assertEquals(setOf("arg:p2", "this.value", "v2"), p.answer("t"))
        assertEquals(setOf("arg:p1"), p.answer("v1"))
        assertEquals(setOf("arg:p2", "t", "this.value"), p.answer("v2"))
    }

    @Test
    fun `today this field write in a method is a weak update`() {
        val p = probeAt(THIS_WRITES, "method", "t", "v1", "v2")
        assertEquals(setOf("arg:p1", "arg:p2", "this.value", "v1", "v2"), p.answer("t"))
        assertEquals(setOf("arg:p1", "arg:p2", "t", "this.value", "v2"), p.answer("v1"))
    }

    @Test
    fun `today a source self assignment leaves no self copy in JIR and x keeps z`() {
        val p = probeAt(SAMPLE, "selfCopyAlloc", "x", "z")
        assertEquals(0, p.selfCopies())
        assertEquals(setOf("new(%0#0)", "z"), p.answer("x"))
        assertEquals(setOf("new(%0#0)", "x"), p.answer("z"))
    }

    @Test
    fun `today a source self assignment of an argument copy leaves no self copy in JIR and x keeps z`() {
        val p = probeAt(SAMPLE, "selfCopyArg", "x", "z")
        assertEquals(0, p.selfCopies())
        assertEquals(setOf("arg:p", "z"), p.answer("x"))
        assertEquals(setOf("arg:p", "x"), p.answer("z"))
    }

    @Test
    fun `today a self cast gets a new JIR local and x keeps z`() {
        val p = probeAt(SAMPLE, "selfCast", "x", "z")
        assertEquals(0, p.selfCopies())
        assertEquals(setOf("new(z)", "z"), p.answer("x"))
        assertEquals(setOf("new(z)", "x"), p.answer("z"))
    }

    @Test
    fun `today JIR of jdk and sample classes has no self copy and no load into its own instance`() {
        var methods = 0
        var selfCopies = 0
        var selfLoads = 0
        for (name in SCAN_CLASSES) {
            val cls = cp.findClassOrNull(name) ?: continue
            for (m in cls.declaredMethods + cls.innerClasses.flatMap { it.declaredMethods }) {
                val insts = runCatching { m.instList }.getOrNull() ?: continue
                methods++
                selfCopies += insts.count { it.isSelfCopy() }
                selfLoads += insts.count { it.isSelfLoad() }
            }
        }
        println("scan: methods=$methods selfCopies=$selfCopies selfLoads=$selfLoads")
        assertTrue(methods > 1000)
        assertEquals(0, selfCopies)
        assertEquals(0, selfLoads)
    }

    @Test
    fun `today load into the live root of the instance group makes a self loop and drops the aliased load`() {
        val p = probeAt(SAMPLE, "reprLoadRightAfterCopy", "x", "w")
        assertEquals(nexts("x", 1..6), p.answer("x"))
        assertEquals(setOf("arg:p.next"), p.answer("w"))
        assertEquals(setOf("x"), p.heapAnswer("x", BOX, "next", BOX))
    }

    @Test
    fun `today load into the live root of the instance group without a prior load makes a self loop`() {
        val p = probeAt(SAMPLE, "reprLoadRightAfterCopyAlone", "x")
        assertEquals(nexts("x", 1..6), p.answer("x"))
        assertEquals(setOf("x"), p.heapAnswer("x", BOX, "next", BOX))
    }

    @Test
    fun `today conditional load into the root merges p with its next chain`() {
        val p = probeAt(SAMPLE, "reprLoadConditional", "x", "w")
        assertEquals(nexts("arg:p", 0..6) + nexts("w", 0..6) + nexts("x", 1..6), p.answer("x"))
        assertEquals(nexts("arg:p", 0..6) + nexts("w", 1..6) + nexts("x", 0..6), p.answer("w"))
    }

    @Test
    fun `today load into a dead local after a copy keeps the aliased load`() {
        val p = probeAt(SAMPLE, "reprLoadOther", "x", "w")
        assertEquals(setOf("arg:p.next", "w"), p.answer("x"))
        assertEquals(setOf("arg:p.next", "x"), p.answer("w"))
    }

    @Test
    fun `today JIR splits a load into a live local through a temporary and the aliased load is kept`() {
        val direct = probeAt(SAMPLE, "reprLoadIntoLiveRoot", "x", "w")
        assertEquals(setOf("arg:p.next", "w"), direct.answer("x"))
        assertEquals(setOf("arg:p.next", "x"), direct.answer("w"))
        val heap = probeAt(SAMPLE, "reprLoadIntoLiveRootHeap", "x", "w", "y")
        assertEquals(setOf("arg:h.box.next", "w", "y.next"), heap.answer("x"))
        assertEquals(setOf("arg:h.box"), heap.answer("y"))
    }

    @Test
    fun `today self load in source gets a JIR temporary and the aliased load is kept`() {
        val arg = probeAt(SAMPLE, "reprLoadArg", "x", "w")
        assertEquals(setOf("arg:p.next", "w"), arg.answer("x"))
        val alloc = probeAt(SAMPLE, "reprLoadAlloc", "x", "w")
        assertEquals(setOf("new(%2#2)", "w"), alloc.answer("x"))
        val cast = probeAt(SAMPLE, "reprLoadCast", "x", "w")
        assertEquals(setOf("arg:p.value", "w"), cast.answer("x"))
        val otherHeap = probeAt(SAMPLE, "reprLoadOtherHeap", "x", "w", "y")
        assertEquals(setOf("arg:h.box.next", "w", "y.next"), otherHeap.answer("x"))
        val otherAlloc = probeAt(SAMPLE, "reprLoadOtherAlloc", "x", "w", "y")
        assertEquals(setOf("new(%2#2)", "w", "y.next"), otherAlloc.answer("x"))
    }

    @Test
    fun `today linked list walk merges cur with head and every next chain`() {
        val p = probeAt(SAMPLE, "listWalk", "cur")
        assertEquals(nexts("arg:head", 0..6) + nexts("cur", 1..6), p.answer("cur"))
        assertEquals(setOf("arg:head", "cur"), p.heapAnswer("cur", BOX, "next", BOX))
    }

    @Test
    fun `today linked list walk merges cur with the second node`() {
        val walkCur = nexts("arg:head", 0..6) + nexts("cur", 1..6) + nexts("second", 0..6)
        val walk = probeAt(SAMPLE, "listWalkWithSecond", "cur", "second")
        assertEquals(walkCur, walk.answer("cur"))
        val steps = probeAt(SAMPLE, "listStepsWithSecond", "cur", "second")
        assertEquals(walkCur, steps.answer("cur"))
        val conditional = probeAt(SAMPLE, "reprLoadInLoop", "cur", "second")
        assertEquals(walkCur, conditional.answer("cur"))
        val liveRoot = probeAt(SAMPLE, "reprLoadIntoLiveRootLoop", "cur", "second")
        assertEquals(walkCur, liveRoot.answer("cur"))
    }

    @Test
    fun `today a loop at the method start gets a JIR goto so no back edge reaches the first instruction`() {
        val p = probeAt(SAMPLE, "loopAtFirstInstruction", "t", "v", "b")
        assertEquals(1, p.loopHeadAfterEntryGoto())
        assertEquals(setOf("b.value", "new(v)", "static:DirectedAliasSample.staticBox.value", "v"), p.answer("t"))
        assertEquals(setOf("b.value", "new(v)", "static:DirectedAliasSample.staticBox.value", "t"), p.answer("v"))
        assertEquals(setOf("static:DirectedAliasSample.staticBox"), p.answer("b"))
        assertEquals(setOf("new(v)", "t", "v"), p.heapAnswer("b", BOX, "value"))
    }

    @Test
    fun `today catch after a throwing call reads the field that the try block wrote`() {
        val p = probeAt(SAMPLE, "catchAfterThrowingCall", "t", "v", "x")
        assertEquals(setOf("arg:pv", "v", "x.value"), p.answer("t"))
        assertEquals(setOf("arg:pv", "t", "x.value"), p.answer("v"))
        assertEquals(setOf("new(x)"), p.answer("x"))
        assertEquals(setOf("arg:pv", "t", "v"), p.heapAnswer("x", BOX, "value"))
    }

    @Test
    fun `today static write is ignored in a generic class`() {
        val p = probeAt(GENERIC_STATICS, "staticWriteThenRead", "t", "v")
        assertEquals(setOf("static:GenericStatics<T>.genericStatic"), p.answer("t"))
        assertEquals(setOf("new(v)"), p.answer("v"))
        assertEquals(setOf("sample.alias.DirectedAliasSample.GenericStatics<T>"), p.staticTypeNames("t"))
    }

    @Test
    fun `today static write is ignored in a nested class`() {
        val p = probeAt(NESTED_STATICS, "staticWriteThenRead", "t", "v")
        assertEquals(setOf("static:NestedStatics\$Inner.innerStatic"), p.answer("t"))
        assertEquals(setOf("new(v)"), p.answer("v"))
        assertEquals(
            setOf("sample.alias.DirectedAliasSample.NestedStatics.NestedStatics\$Inner"),
            p.staticTypeNames("t")
        )
    }

    @Test
    fun `today vararg string constants are the element aliases of the vararg array`() {
        val p = probeAt(SAMPLE, "varargStringConstants", "values", callee = VARARGS)
        assertEquals(setOf("const:a", "const:b", "values[*]"), p.elementAnswer("values"))
    }

    @Test
    fun `today vararg boxed constants are the element aliases of the vararg array`() {
        val p = probeAt(SAMPLE, "varargBoxedConstants", "values", callee = VARARGS)
        assertEquals(setOf("new(%1#1)", "new(%2#2)", "values[*]"), p.elementAnswer("values"))
        assertEquals(
            setOf("java.lang.Boolean.valueOf(1)", "java.lang.Integer.valueOf(1)"),
            p.elementAllocCalls("values")
        )
    }

    @Test
    fun `mode directed is accepted by params`() {
        val defaults = JIRLocalAliasAnalysis.Params()
        assertEquals(AliasAnalysisMode.DSU, defaults.mode)
        assertEquals(7, defaults.symDepth)
        assertEquals(6, defaults.maxAccessors)
        assertEquals(10_000, defaults.maxCallClosure)

        val directed = JIRLocalAliasAnalysis.Params(mode = AliasAnalysisMode.DIRECTED)
        assertEquals(AliasAnalysisMode.DIRECTED, directed.mode)

        val method = findMethod(SAMPLE, "heapChainAllocs")
        val call = method.instList.filterIsInstance<JIRCallInst>().first { it.callExpr.method.name == PROBE }
        val z = AccessPathBase.LocalVar((call.callExpr.args[0] as JIRLocalVar).index)
        // The directed backend answers. For this method its answer has the elements of the DSU answer.
        val aa = aaForMethod(method, noRules, directed)
        assertEquals(dsuForMethod(method).findAlias(z, call)?.toSet(), aa.findAlias(z, call)?.toSet())
    }

    @Test
    fun `alias analysis mode names are parsed and unknown names fail`() {
        assertEquals(AliasAnalysisMode.DSU, AliasAnalysisMode.parse("dsu"))
        assertEquals(AliasAnalysisMode.SHADOW, AliasAnalysisMode.parse("SHADOW"))
        assertEquals(AliasAnalysisMode.DIRECTED, AliasAnalysisMode.parse("Directed"))
        assertFailsWith<IllegalArgumentException> { AliasAnalysisMode.parse("fast") }
    }

    @Test
    fun `vararg element aliases equal the group answer in dsu mode`() {
        val cases = listOf(
            Triple("varargStringConstants", VARARGS, 0),
            Triple("varargBoxedConstants", VARARGS, 0),
            Triple("catchAfterThrowingCall", PROBE, 2),
        )
        for ((methodName, callee, argIdx) in cases) {
            val method = findMethod(SAMPLE, methodName)
            val call = method.instList.filterIsInstance<JIRCallInst>().first { it.callExpr.method.name == callee }
            val base = AccessPathBase.LocalVar((call.callExpr.args[argIdx] as JIRLocalVar).index)
            val dsu = dsuForMethod(method)
            val group = dsu.getAllAliasAtStatement(call).firstOrNull { set ->
                set.any { it is AliasApInfo && it.base == base && it.accessors.singleOrNull() is AliasAccessor.Array }
            }
            val facade = aaForMethod(method, noRules, JIRLocalAliasAnalysis.Params(mode = AliasAnalysisMode.DSU))
            assertEquals(group, facade.findArrayElementAliases(base, call), methodName)
        }
    }

    private fun nexts(base: String, counts: IntRange): Set<String> =
        counts.map { base + ".next".repeat(it) }.toSet()

    private fun JIRInst.isSelfCopy(): Boolean {
        if (this !is JIRAssignInst) return false
        val lhv = lhv as? JIRLocalVar ?: return false
        val source = (rhv as? JIRCastExpr)?.operand ?: rhv
        return source is JIRLocalVar && source.index == lhv.index
    }

    private fun JIRInst.isSelfLoad(): Boolean {
        if (this !is JIRAssignInst) return false
        val lhv = lhv as? JIRLocalVar ?: return false
        val instance = when (val source = (rhv as? JIRCastExpr)?.operand ?: rhv) {
            is JIRFieldRef -> source.instance
            is JIRArrayAccess -> source.array
            else -> null
        }
        return instance is JIRLocalVar && instance.index == lhv.index
    }

    private inner class Probe(
        val method: JIRMethod,
        val aa: JIRLocalAliasAnalysis,
        val call: JIRCallInst,
        val roles: List<String>,
    ) {
        private val values = method.instList.flatMap { inst -> inst.operands.flatMap { it.allValues() } }

        private val roleOfLocal: Map<Int, String> = roles.indices
            .associate { (call.callExpr.args[it] as JIRLocalVar).index to roles[it] }

        private val localNames: Map<Int, String> = values
            .filterIsInstance<JIRLocalVar>()
            .associate { it.index to (roleOfLocal[it.index] ?: "${it.name}#${it.index}") }

        private val argNames: Map<Int, String> = values
            .filterIsInstance<JIRArgument>()
            .associate { it.index to it.name }

        private fun local(role: String): JIRLocalVar = call.callExpr.args[roles.indexOf(role)] as JIRLocalVar

        fun aliases(role: String): List<AliasInfo>? =
            aa.findAlias(AccessPathBase.LocalVar(local(role).index), call)

        fun answer(role: String): Set<String>? = aliases(role)?.map { it.show() }?.toSortedSet()

        fun heapAnswer(role: String, fieldClass: String, field: String, fieldType: String = OBJECT): Set<String> {
            val local = local(role)
            val accessor = AliasAccessor.Field(fieldClass, field, fieldType)
            val result = aa.findHeapAlias(AccessPathBase.LocalVar(local.index), listOf(accessor), call)
                .orEmpty().map { it.show() }.toSortedSet()
            println("  heap($role.$field) = $result")
            return result
        }

        fun selfCopies(): Int = method.instList.count { it.isSelfCopy() }

        /**
         * Checks the JIR shape of a loop at the method start: the first instruction is a `goto` with no
         * predecessor, and its target is a loop head. Returns the index of the loop head.
         */
        fun loopHeadAfterEntryGoto(): Int {
            val flow = method.flowGraph()
            val first = method.instList.first()
            assertTrue(first is JIRGotoInst, "The first instruction must be a goto")
            assertTrue(flow.predecessors(first).isEmpty(), "No edge must reach the first instruction")
            val head = flow.successors(first).single()
            assertTrue(flow.predecessors(head).any { it.location.index > head.location.index }, "No back edge")
            return head.location.index
        }

        fun staticTypeNames(role: String): Set<String> = aliases(role).orEmpty()
            .filterIsInstance<AliasApInfo>()
            .filter { it.base == AccessPathBase.ClassStatic }
            .flatMap { info -> info.accessors.filterIsInstance<AliasAccessor.Static>().map { it.typeName } }
            .toSortedSet()

        /**
         * The element aliases of the array in [role], as the vararg branch of
         * `JIRBasicAtomEvaluator.resolveLocalVarValue` gets them (`findArrayElementAliases`).
         */
        fun elementAliases(role: String): List<AliasInfo>? =
            aa.findArrayElementAliases(AccessPathBase.LocalVar(local(role).index), call)

        fun elementAnswer(role: String): Set<String>? = elementAliases(role)?.map { it.show() }?.toSortedSet()

        fun elementAllocCalls(role: String): Set<String> = elementAliases(role).orEmpty()
            .filterIsInstance<AliasAllocInfo>()
            .mapNotNull { method.instList[it.allocInst].callExpr?.toString() }
            .toSortedSet()

        fun render(): String = buildString {
            appendLine("=== ${method.enclosingClass.simpleName}.${method.name}")
            method.instList.forEachIndexed { idx, inst ->
                val locals = inst.operands.flatMap { it.allValues() }.filterIsInstance<JIRLocalVar>()
                    .map { "${it.name}#${it.index}" }.distinct()
                appendLine("  $idx: $inst" + if (locals.isEmpty()) "" else "    [${locals.joinToString(", ")}]")
            }
            roles.forEach { role ->
                appendLine("  alias($role) = ${aliases(role)?.map { it.show() }}")
            }
        }

        private fun AliasInfo.show(): String = when (this) {
            is AliasAllocInfo -> "new(${allocTarget(allocInst)})"
            is AliasApInfo -> base.show() + accessors.joinToString("") { it.show() }
        }

        private fun allocTarget(idx: Int): String = when (val inst = method.instList[idx]) {
            is JIRAssignInst -> (inst.lhv as? JIRLocalVar)?.let { localNames[it.index] } ?: inst.lhv.toString()
            is JIRCatchInst -> "catch ${inst.throwable}"
            else -> "#$idx"
        }

        private fun AccessPathBase.show(): String = when (this) {
            is AccessPathBase.LocalVar -> localNames[idx] ?: "local#$idx"
            is AccessPathBase.Argument -> "arg:" + (argNames[idx] ?: "#$idx")
            is AccessPathBase.This -> "this"
            is AccessPathBase.ClassStatic -> "static"
            is AccessPathBase.Constant -> "const:$value"
            else -> toString()
        }

        private fun AliasAccessor.show(): String = when (this) {
            is AliasAccessor.Field -> ".$fieldName"
            is AliasAccessor.Array -> "[*]"
            is AliasAccessor.Static -> ":" + typeName.substringAfterLast('.')
        }
    }

    private fun JIRExpr.allValues(): List<JIRExpr> = listOf(this) + operands.flatMap { it.allValues() }

    private fun probeAt(
        className: String,
        methodName: String,
        vararg roles: String,
        rules: TaintRulesProvider = noRules,
        callee: String = PROBE,
    ): Probe {
        val method = findMethod(className, methodName)
        val call = method.instList.filterIsInstance<JIRCallInst>().first { it.callExpr.method.name == callee }
        check(call.callExpr.args.size == roles.size) { "Probe arity mismatch in $methodName" }
        return Probe(method, aaForMethod(method, rules), call, roles.toList()).also { println(it.render()) }
    }

    private fun aaForMethod(
        method: JIRMethod,
        rules: TaintRulesProvider,
        params: JIRLocalAliasAnalysis.Params = testParams(),
    ): JIRLocalAliasAnalysis {
        val ep = method.instList.first()
        val graph = JApplicationGraphImpl(cp, runBlocking { cp.usagesExt() })
        val callResolver = JIRCallResolver(cp, SingleLocationUnit(method.enclosingClass.declaration.location))
        val localReachability = JIRLocalVariableReachability(method, graph, manager)
        val cancellation = Cancellation().also { it.activate() }
        checkDirectedPostFix(ep, graph, callResolver, rules, localReachability, cancellation, manager, params)
        return JIRLocalAliasAnalysis(ep, graph, callResolver, rules, localReachability, cancellation, manager, params)
    }

    private fun dsuForMethod(method: JIRMethod): JIRDsuAliasAnalysis {
        val ep = method.instList.first()
        val graph = JApplicationGraphImpl(cp, runBlocking { cp.usagesExt() })
        val callResolver = JIRCallResolver(cp, SingleLocationUnit(method.enclosingClass.declaration.location))
        val localReachability = JIRLocalVariableReachability(method, graph, manager)
        val cancellation = Cancellation().also { it.activate() }
        return JIRDsuAliasAnalysis(
            ep, graph, callResolver, noRules, localReachability, cancellation, manager, JIRLocalAliasAnalysis.Params()
        )
    }

    private fun testParams() = JIRLocalAliasAnalysis.Params(mode = AliasAnalysisMode.fromTestProperty())

    private class SingleLocationUnit(val loc: RegisteredLocation) : JIRUnitResolver {
        override fun resolve(method: JIRMethod): UnitType =
            if (method.enclosingClass.declaration.location == loc) SingletonUnit else UnknownUnit

        override fun locationIsUnknown(loc: RegisteredLocation): Boolean = loc != this.loc
    }

    companion object {
        private const val SAMPLE = "sample.alias.DirectedAliasSample"
        private const val BOX = "$SAMPLE\$Box"
        private const val CTOR_LOOP = "$SAMPLE\$CtorLoop"
        private const val CTOR_JOIN = "$SAMPLE\$CtorJoin"
        private const val THIS_WRITES = "$SAMPLE\$ThisWrites"
        private const val GENERIC_STATICS = "$SAMPLE\$GenericStatics"
        private const val NESTED_STATICS = "$SAMPLE\$NestedStatics"
        private const val VARARGS = "varargs"
        private const val OBJECT = "java.lang.Object"
        private const val PROBE = "probe"

        private val SCAN_CLASSES = listOf(
            "java.util.LinkedList", "java.util.HashMap", "java.util.TreeMap", "java.util.ArrayDeque",
            "java.util.concurrent.ConcurrentHashMap", "java.lang.String", "java.lang.AbstractStringBuilder",
            "java.util.Collections", "java.util.Arrays", "java.util.ArrayList", "java.util.LinkedHashMap",
            "java.util.PriorityQueue", "java.util.regex.Pattern", "java.util.regex.Matcher", "java.math.BigInteger",
            "java.util.concurrent.ConcurrentLinkedQueue", "java.util.concurrent.LinkedBlockingQueue",
            "java.util.IdentityHashMap", "java.util.WeakHashMap", "java.util.Hashtable", "java.util.TreeSet",
            "java.lang.Class", "java.lang.ClassLoader", "java.lang.Thread", "java.lang.Throwable",
            "java.io.File", "java.net.URI", "java.util.Formatter", "java.util.Scanner", "java.util.Properties",
            "sample.alias.DirectedAliasSample", "sample.alias.LoopAliasSample", "sample.alias.HeapAliasSample",
            "sample.alias.FlakyAliasSample", "sample.alias.HeaderValuesHangSample", "sample.alias.InterProcAliasSample",
        )
    }
}
