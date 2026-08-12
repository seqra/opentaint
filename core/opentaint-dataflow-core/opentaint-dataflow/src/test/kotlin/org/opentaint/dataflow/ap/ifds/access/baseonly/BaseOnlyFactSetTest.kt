package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.serialization.MethodContextSerializer
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class BaseOnlyFactSetTest {
    private val mark = TaintMarkAccessor("m")
    private val field1 = FieldAccessor("A", "f", "B")
    private val field2 = FieldAccessor("A", "g", "B")

    private fun mkManager(
        fieldSensitive: Boolean = false,
        fieldGeneralizationEnabled: Boolean = true,
        summaryStorageFieldGeneralizationEnabled: Boolean = false,
    ) = BaseOnlyApManager(
        AnyAccessorUnrollStrategy.AnyAccessorDisabled,
        org.opentaint.dataflow.util.Cancellation(),
        fieldSensitive = fieldSensitive,
        fieldGeneralizationEnabled = fieldGeneralizationEnabled,
        summaryStorageFieldGeneralizationEnabled = summaryStorageFieldGeneralizationEnabled,
    )

    private val dummyMethod = object : CommonMethod {
        override val name: String = "dummy"
        override val parameters: List<CommonMethodParameter> = emptyList()
        override val returnType: CommonTypeName = object : CommonTypeName {
            override val typeName: String = "void"
        }

        override fun flowGraph(): ControlFlowGraph<CommonInst> = object : ControlFlowGraph<CommonInst> {
            override val instructions: List<CommonInst> = emptyList()
            override val entries: List<CommonInst> = emptyList()
            override val exits: List<CommonInst> = emptyList()
            override fun successors(node: CommonInst): Set<CommonInst> = emptySet()
            override fun predecessors(node: CommonInst): Set<CommonInst> = emptySet()
        }
    }

    private val inst = object : CommonInst {
        override fun toString(): String = "i0"
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val method: CommonMethod = dummyMethod
        }
    }

    private val lm = object : LanguageManager {
        override fun getInstIndex(inst: CommonInst): Int = 0
        override fun getMaxInstIndex(method: CommonMethod): Int = 0
        override fun getInstByIndex(method: CommonMethod, index: Int): CommonInst = error("unused")
        override fun isEmpty(method: CommonMethod): Boolean = error("unused")
        override fun getCallExpr(inst: CommonInst): CommonCallExpr? = null
        override fun producesExceptionalControlFlow(inst: CommonInst): Boolean = false
        override fun getCalleeMethod(callExpr: CommonCallExpr): CommonMethod = error("unused")
        override val methodContextSerializer: MethodContextSerializer get() = error("unused")
    }

    private fun BaseOnlyApManager.finalFact(base: AccessPathBase, vararg accessors: Accessor): FinalFactAp {
        var fact = createFinalAp(base, ExclusionSet.Universe)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    @Test
    fun `z2f canonicalizes explicit Any to the implicit structural branch`() {
        val m = mkManager()
        val set = m.methodEdgesFinalApSet(inst, 0, lm)

        val anyMark = m.finalFact(AccessPathBase.This, AnyAccessor, mark)
        val added1 = set.add(inst, anyMark)
        assertNotNull(added1, "first add returns a fact")
        assertTrue(added1.startsWithAccessor(field1), "returned fact is any-expanded (field insensitive)")

        val bareMark = m.finalFact(AccessPathBase.This, mark)
        assertNull(set.add(inst, bareMark), "explicit Any and implicit Any have one storage key")

        val collected = mutableListOf<FinalFactAp>()
        set.collectApAtStatement(collected, inst)
        assertEquals(1, collected.size)
    }

    @Test
    fun `z2f preserves the implicit structural branch of a bare mark`() {
        val m = mkManager()
        val set = m.methodEdgesFinalApSet(inst, 0, lm)
        val added = set.add(inst, m.finalFact(AccessPathBase.This, mark))
        assertNotNull(added)
        assertTrue(added.startsWithAccessor(field1))
    }

    @Test
    fun `z2f keeps distinct fields when field extension enabled`() {
        val m = mkManager(fieldSensitive = true)
        val set = m.methodEdgesFinalApSet(inst, 0, lm)
        assertNotNull(set.add(inst, m.finalFact(AccessPathBase.This, field1, mark)))
        assertNotNull(set.add(inst, m.finalFact(AccessPathBase.This, field2, mark)), "distinct field kept under extension")
    }

    @Test
    fun `f2f dedups and returns on new edge`() {
        val m = mkManager()
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val initial = m.mostAbstractInitialAp(AccessPathBase.Return).replaceExclusions(ExclusionSet.Empty)
        val final = m.createFinalAp(AccessPathBase.This, ExclusionSet.Empty).prependAccessor(mark)

        assertEquals(1, set.add(inst, initial, final).size, "first f2f edge is new")
        assertTrue(set.add(inst, initial, final).isEmpty(), "same f2f edge subsumed")

        val collected = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        set.collectApAtStatement(collected, inst)
        assertEquals(1, collected.size)
    }

    @Test
    fun `f2f keeps a final coverage antichain`() {
        val m = mkManager(fieldSensitive = true)
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val initial = m.mostAbstractInitialAp(AccessPathBase.Return).replaceExclusions(ExclusionSet.Empty)
        val fieldFinal = m.finalFact(AccessPathBase.This, field1, mark)
            .replaceExclusions(ExclusionSet.Empty)
        val generalFinal = m.finalFact(AccessPathBase.This, mark)
            .replaceExclusions(ExclusionSet.Empty)

        assertEquals(listOf(initial to fieldFinal), set.add(inst, initial, fieldFinal))
        assertEquals(listOf(initial to generalFinal), set.add(inst, initial, generalFinal))
        assertTrue(
            set.add(inst, initial, fieldFinal).isEmpty(),
            "a final already covered by the stored abstract final is not republished",
        )

        val collected = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        set.collectApAtStatement(collected, inst)
        assertEquals(listOf(initial to generalFinal), collected)
    }

    @Test
    fun `covered final still contributes to shared exclusion state`() {
        val m = mkManager(fieldSensitive = true)
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val ex1 = ExclusionSet.Concrete(TaintMarkAccessor("excluded-general"))
        val ex2 = ExclusionSet.Concrete(TaintMarkAccessor("excluded-covered"))
        val initial1 = m.mostAbstractInitialAp(AccessPathBase.Return).replaceExclusions(ex1)
        val initial2 = initial1.replaceExclusions(ex2)
        val generalFinal = m.finalFact(AccessPathBase.This, mark).replaceExclusions(ex1)
        val coveredFinal = m.finalFact(AccessPathBase.This, field1, mark).replaceExclusions(ex2)

        assertEquals(listOf(initial1 to generalFinal), set.add(inst, initial1, generalFinal))
        val delta = set.add(inst, initial2, coveredFinal)

        assertEquals(1, delta.size)
        assertEquals(ex1.union(ex2), delta.single().first.exclusions)
        assertEquals(ex1.union(ex2), delta.single().second.exclusions)
        assertTrue(
            BaseOnlyAccessOps.covers(
                (delta.single().second as BaseOnlyFinalFactAp).access,
                (coveredFinal as BaseOnlyFinalFactAp).access,
            )
        )
    }

    @Test
    fun `f2f shares Tree fact-state exclusion union across its final language`() {
        val m = mkManager(fieldSensitive = true)
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val ex1 = ExclusionSet.Concrete(TaintMarkAccessor("excluded-1"))
        val ex2 = ExclusionSet.Concrete(TaintMarkAccessor("excluded-2"))
        val initial1 = m.mostAbstractInitialAp(AccessPathBase.Return).replaceExclusions(ex1)
        val initial2 = initial1.replaceExclusions(ex2)
        val final1 = m.finalFact(AccessPathBase.This, field1, mark).replaceExclusions(ex1)
        val final2 = m.finalFact(AccessPathBase.This, field2, mark).replaceExclusions(ex2)

        assertEquals(1, set.add(inst, initial1, final1).size)
        val delta = set.add(inst, initial2, final2)
        assertEquals(2, delta.size, "an exclusion change re-emits the complete final language")
        assertTrue(delta.all { it.first.exclusions == ex1.union(ex2) })
        assertTrue(delta.all { it.second.exclusions == ex1.union(ex2) })

        val collected = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        set.collectApAtStatement(collected, inst)
        assertEquals(2, collected.size)
        assertTrue(collected.all { it.first.exclusions == ex1.union(ex2) })
        assertTrue(collected.all { it.second.exclusions == ex1.union(ex2) })
    }

    @Test
    fun `f2f exclusion update retains Normal and Value finals separately`() {
        val m = mkManager(fieldSensitive = true)
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val ex1 = ExclusionSet.Concrete(TaintMarkAccessor("excluded-direct"))
        val ex2 = ExclusionSet.Concrete(TaintMarkAccessor("excluded-wrapped"))
        val initial1 = m.mostAbstractInitialAp(AccessPathBase.Return).replaceExclusions(ex1)
        val initial2 = initial1.replaceExclusions(ex2)
        val normal = m.finalFact(AccessPathBase.This, mark).replaceExclusions(ex1) as BaseOnlyFinalFactAp
        val value = m.finalFact(AccessPathBase.This, ValueAccessor, mark)
            .replaceExclusions(ex2) as BaseOnlyFinalFactAp

        assertEquals(BaseOnlyValueAccessorState.Normal, normal.access.valueAccessorState)
        assertEquals(BaseOnlyValueAccessorState.Value, value.access.valueAccessorState)
        assertEquals(1, set.add(inst, initial1, normal).size)
        val delta = set.add(inst, initial2, value)
        assertEquals(2, delta.size, "Normal and Value finals must both be re-emitted")
        assertEquals(
            setOf(BaseOnlyValueAccessorState.Normal, BaseOnlyValueAccessorState.Value),
            delta.map { (it.second as BaseOnlyFinalFactAp).access.valueAccessorState }.toSet(),
        )
        assertTrue(delta.all { it.second.exclusions == ex1.union(ex2) })

        val collected = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        set.collectApAtStatement(collected, inst)
        assertEquals(2, collected.size)
        assertEquals(
            setOf(BaseOnlyValueAccessorState.Normal, BaseOnlyValueAccessorState.Value),
            collected.map { (it.second as BaseOnlyFinalFactAp).access.valueAccessorState }.toSet(),
        )
        assertTrue(collected.all { it.second.exclusions == ex1.union(ex2) })
    }

    @Test
    fun `method edges publish every BaseOnly final changed by exclusion aggregation`() {
        val m = mkManager(fieldSensitive = true)
        val methodEntryPoint = MethodEntryPoint(EmptyMethodContext, inst)
        val edges = MethodAnalyzerEdges(m, methodEntryPoint, lm)
        val ex1 = ExclusionSet.Concrete(TaintMarkAccessor("excluded-direct"))
        val ex2 = ExclusionSet.Concrete(TaintMarkAccessor("excluded-wrapped"))
        val initial1 = m.mostAbstractInitialAp(AccessPathBase.Return).replaceExclusions(ex1)
        val initial2 = initial1.replaceExclusions(ex2)
        val normal = m.finalFact(AccessPathBase.This, mark).replaceExclusions(ex1)
        val value = m.finalFact(AccessPathBase.This, ValueAccessor, mark).replaceExclusions(ex2)

        assertEquals(1, edges.add(Edge.FactToFact(methodEntryPoint, initial1, inst, normal)).size)
        val delta = edges.add(Edge.FactToFact(methodEntryPoint, initial2, inst, value))

        assertEquals(2, delta.size)
        val factEdges = delta.map { it as Edge.FactToFact }
        assertTrue(factEdges.all { it.initialFactAp.exclusions == ex1.union(ex2) })
        assertTrue(factEdges.all { it.factAp.exclusions == ex1.union(ex2) })
        assertEquals(
            setOf(BaseOnlyValueAccessorState.Normal, BaseOnlyValueAccessorState.Value),
            factEdges.map { (it.factAp as BaseOnlyFinalFactAp).access.valueAccessorState }.toSet(),
        )
    }

    @Test
    fun `f2f trace lookup resolves a suffix alias to its field abstract primary`() {
        val m = mkManager(fieldSensitive = true)
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val primary = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.Return,
            packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR),
            ExclusionSet.Empty,
        )
        val alias = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.Return,
            ABSTRACT_EMPTY_ACCESS,
            ExclusionSet.Empty,
        )
        val final = m.finalFact(AccessPathBase.This, field1, mark).replaceExclusions(ExclusionSet.Empty)

        assertEquals(1, set.add(inst, primary, final).size)
        m.enableTraceResolutionMode()

        val collected = mutableListOf<FinalFactAp>()
        set.collectApAtStatement(
            collected,
            inst,
            alias,
            m.mostAbstractInitialAp(AccessPathBase.This),
        )
        assertEquals(listOf(final), collected)
    }

    @Test
    fun `f2f publishes correlated edges with different exact initial accesses`() {
        val m = mkManager(fieldSensitive = true)
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val initialField = m.interner.index(FieldAccessor("Input", "field", "Value"))
        val finalField = m.interner.index(FieldAccessor("Output", "field", "Value"))
        val terminal = m.interner.index(TaintMarkAccessor("correlated-terminal"))
        val broadInitial = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.This,
            packBaseOnlyAccess(NO_ACCESSOR, initialField, ABSTRACT_MARK),
            ExclusionSet.Empty,
        )
        val broadFinal = BaseOnlyFinalFactAp(
            m,
            AccessPathBase.Return,
            packBaseOnlyAccess(NO_ACCESSOR, finalField, ABSTRACT_MARK),
            ExclusionSet.Empty,
        )
        val concreteInitial = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.This,
            packBaseOnlyAccess(NO_ACCESSOR, initialField, terminal),
            ExclusionSet.Empty,
        )
        val concreteFinal = BaseOnlyFinalFactAp(
            m,
            AccessPathBase.Return,
            packBaseOnlyAccess(NO_ACCESSOR, finalField, terminal),
            ExclusionSet.Empty,
        )

        assertEquals(listOf(broadInitial to broadFinal), set.add(inst, broadInitial, broadFinal))
        assertEquals(
            listOf(concreteInitial to concreteFinal),
            set.add(inst, concreteInitial, concreteFinal),
            "summary-edge subsumption must not suppress an intraprocedural exact-initial edge",
        )

        val all = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        set.collectApAtStatement(all, inst)
        assertEquals(setOf(broadInitial to broadFinal, concreteInitial to concreteFinal), all.toSet())

        val concreteLookup = mutableListOf<FinalFactAp>()
        set.collectApAtStatement(
            concreteLookup,
            inst,
            concreteInitial,
            m.mostAbstractInitialAp(AccessPathBase.Return),
        )
        assertEquals(listOf<FinalFactAp>(concreteFinal), concreteLookup)
    }

    @Test
    fun `f2f final pattern lookup remains exact after final index promotion`() {
        val m = mkManager(fieldSensitive = true)
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val initial = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.This,
            ABSTRACT_EMPTY_ACCESS,
            ExclusionSet.Empty,
        )
        val terminal = m.interner.index(TaintMarkAccessor("indexed-terminal"))
        val finals = (0 until 64).map { index ->
            BaseOnlyFinalFactAp(
                m,
                AccessPathBase.Return,
                packBaseOnlyAccess(
                    NO_ACCESSOR,
                    m.interner.index(FieldAccessor("Indexed", "field$index", "Value")),
                    terminal,
                ),
                ExclusionSet.Empty,
            ).also { set.add(inst, initial, it) }
        }
        val selected = finals[47]
        val pattern = BaseOnlyInitialFactAp(
            m,
            selected.base,
            selected.access,
            ExclusionSet.Empty,
        )

        val collected = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        set.collectApAtStatement(collected, inst, pattern)

        assertEquals(listOf<Pair<InitialFactAp, FinalFactAp>>(initial to selected), collected)
    }

    @Test
    fun `f2f trace lookup erases an eligible exact witness without changing forward state`() {
        val m = mkManager(fieldSensitive = true)
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val initialField = m.interner.index(FieldAccessor("Input", "field", "Value"))
        val finalField = m.interner.index(FieldAccessor("Output", "field", "Value"))
        val otherInitialField = m.interner.index(FieldAccessor("Input", "other", "Value"))
        val otherFinalField = m.interner.index(FieldAccessor("Output", "other", "Value"))
        val exA = ExclusionSet.Concrete(TaintMarkAccessor("trace-view-a"))
        val exB = ExclusionSet.Concrete(TaintMarkAccessor("trace-view-b"))
        val preciseInitial = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.This,
            packBaseOnlyAccess(NO_ACCESSOR, initialField, ABSTRACT_MARK),
            exA,
        )
        val preciseFinal = BaseOnlyFinalFactAp(
            m,
            AccessPathBase.Return,
            packBaseOnlyAccess(NO_ACCESSOR, finalField, ABSTRACT_MARK),
            exA,
        )
        val otherPreciseInitial = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.This,
            packBaseOnlyAccess(NO_ACCESSOR, otherInitialField, ABSTRACT_MARK),
            exB,
        )
        val otherPreciseFinal = BaseOnlyFinalFactAp(
            m,
            AccessPathBase.Return,
            packBaseOnlyAccess(NO_ACCESSOR, otherFinalField, ABSTRACT_MARK),
            exB,
        )
        val generalizedInitial = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.This,
            ABSTRACT_EMPTY_ACCESS,
            exA.union(exB),
        )
        val generalizedFinal = BaseOnlyFinalFactAp(
            m,
            AccessPathBase.Return,
            ABSTRACT_EMPTY_ACCESS,
            exA.union(exB),
        )

        assertEquals(listOf(preciseInitial to preciseFinal), set.add(inst, preciseInitial, preciseFinal))
        assertEquals(
            listOf(otherPreciseInitial to otherPreciseFinal),
            set.add(inst, otherPreciseInitial, otherPreciseFinal),
        )

        val forwardState = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        set.collectApAtStatement(forwardState, inst)
        assertEquals(
            setOf<Pair<InitialFactAp, FinalFactAp>>(
                preciseInitial to preciseFinal,
                otherPreciseInitial to otherPreciseFinal,
            ),
            forwardState.toSet(),
            "the generalized witness is a trace-only view, not a primary forward edge",
        )

        m.enableTraceResolutionMode()
        val traceLookup = mutableListOf<FinalFactAp>()
        set.collectApAtStatement(
            traceLookup,
            inst,
            generalizedInitial,
            m.mostAbstractInitialAp(AccessPathBase.Return),
        )
        assertEquals(
            listOf<FinalFactAp>(generalizedFinal),
            traceLookup,
            "trace mode exposes a generalized witness without inserting it into the fact set",
        )
    }

    @Test
    fun `f2f field generalization is a trace only view`() {
        val m = mkManager(fieldSensitive = true)
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val exA = ExclusionSet.Concrete(TaintMarkAccessor("generalized-a"))
        val exB = ExclusionSet.Concrete(TaintMarkAccessor("generalized-b"))
        val generalizedExclusion = exA.union(exB)
        val contributors = (0 until MAX_FIELD_ENUMERATION_EDGES + 2).map { index ->
            val field = m.interner.index(FieldAccessor("Input", "field-$index", "Value"))
            val exclusion = if (index % 2 == 0) exA else exB
            val initial = BaseOnlyInitialFactAp(
                m,
                AccessPathBase.Return,
                packBaseOnlyAccess(NO_ACCESSOR, field, ABSTRACT_MARK),
                exclusion,
            )
            val final = BaseOnlyFinalFactAp(
                m,
                AccessPathBase.This,
                ABSTRACT_EMPTY_ACCESS,
                exclusion,
            )
            initial to final
        }

        contributors.forEach { (initial, final) ->
            assertEquals(
                listOf(initial to final),
                set.add(inst, initial, final),
                "forward insertion must retain every exact fact-set edge",
            )
        }

        val generalizedInitial = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.Return,
            ABSTRACT_EMPTY_ACCESS,
            generalizedExclusion,
        )
        val generalizedFinal = BaseOnlyFinalFactAp(
            m,
            AccessPathBase.This,
            ABSTRACT_EMPTY_ACCESS,
            generalizedExclusion,
        )

        val forward = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        set.collectApAtStatement(forward, inst)
        assertEquals(
            contributors.toSet(),
            forward.toSet(),
            "forward collection must remain exact",
        )

        m.enableTraceResolutionMode()
        val traceState = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        set.collectApAtStatement(traceState, inst)
        assertEquals(
            contributors.toSet() + (generalizedInitial to generalizedFinal),
            traceState.toSet(),
            "trace mode adds one generalized view without replacing exact edges",
        )

        val traceLookup = mutableListOf<FinalFactAp>()
        set.collectApAtStatement(
            traceLookup,
            inst,
            generalizedInitial,
            m.mostAbstractInitialAp(AccessPathBase.This),
        )
        assertEquals(listOf<FinalFactAp>(generalizedFinal), traceLookup)
    }

    @Test
    fun `f2f trace view respects disabled field generalization`() {
        val m = mkManager(fieldSensitive = true, fieldGeneralizationEnabled = false)
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val exactInitial = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.Return,
            packBaseOnlyAccess(NO_ACCESSOR, m.interner.index(field1), ABSTRACT_MARK),
            ExclusionSet.Empty,
        )
        val exactFinal = BaseOnlyFinalFactAp(
            m,
            AccessPathBase.This,
            ABSTRACT_EMPTY_ACCESS,
            ExclusionSet.Empty,
        )
        set.add(inst, exactInitial, exactFinal)

        m.enableTraceResolutionMode()

        val traceState = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        set.collectApAtStatement(traceState, inst)
        assertEquals(
            listOf<Pair<InitialFactAp, FinalFactAp>>(exactInitial to exactFinal),
            traceState,
        )

        val generalizedInitial = BaseOnlyInitialFactAp(
            m,
            AccessPathBase.Return,
            ABSTRACT_EMPTY_ACCESS,
            ExclusionSet.Empty,
        )
        val generalizedLookup = mutableListOf<FinalFactAp>()
        set.collectApAtStatement(
            generalizedLookup,
            inst,
            generalizedInitial,
            m.mostAbstractInitialAp(AccessPathBase.This),
        )
        assertTrue(generalizedLookup.isEmpty())
    }

    @Test
    fun `summary and fact trace generalization flags are independent`() {
        fun collectedSizes(
            factTraceGeneralization: Boolean,
            summaryGeneralization: Boolean,
        ): Pair<Int, Int> {
            val manager = mkManager(
                fieldSensitive = true,
                fieldGeneralizationEnabled = factTraceGeneralization,
                summaryStorageFieldGeneralizationEnabled = summaryGeneralization,
            )
            val factSet = manager.methodEdgesInitialToFinalApSet(inst, 0, lm)
            val summaries = manager.methodInitialToFinalApSummariesStorage(inst)
            val entryPoint = MethodEntryPoint(EmptyMethodContext, inst)
            val edges = (0..MAX_FIELD_ENUMERATION_EDGES).map { index ->
                val initial = BaseOnlyInitialFactAp(
                    manager,
                    AccessPathBase.Return,
                    packBaseOnlyAccess(
                        NO_ACCESSOR,
                        manager.interner.index(FieldAccessor("Input", "isolated-$index", "Value")),
                        ABSTRACT_MARK,
                    ),
                    ExclusionSet.Empty,
                )
                val final = BaseOnlyFinalFactAp(
                    manager,
                    AccessPathBase.This,
                    ABSTRACT_EMPTY_ACCESS,
                    ExclusionSet.Empty,
                )
                factSet.add(inst, initial, final)
                Edge.FactToFact(entryPoint, initial, inst, final)
            }

            summaries.add(edges, mutableListOf())
            manager.enableTraceResolutionMode()

            val factViews = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
            factSet.collectApAtStatement(factViews, inst)
            val summaryViews = mutableListOf<FactToFactEdgeBuilder>()
            summaries.filterEdgesTo(
                summaryViews,
                initialFactPattern = null,
                finalFactBase = AccessPathBase.This,
            )
            return factViews.size to summaryViews.size
        }

        assertEquals(
            (MAX_FIELD_ENUMERATION_EDGES + 1) to 1,
            collectedSizes(factTraceGeneralization = false, summaryGeneralization = true),
            "summary generalization must not add a projected fact-set view",
        )
        assertEquals(
            (MAX_FIELD_ENUMERATION_EDGES + 2) to (MAX_FIELD_ENUMERATION_EDGES + 1),
            collectedSizes(factTraceGeneralization = true, summaryGeneralization = false),
            "fact trace generalization must not generalize summary storage",
        )
    }

    @Test
    fun `nd f2f dedups`() {
        val m = mkManager()
        val set = m.methodEdgesNDInitialToFinalApSet(inst, 0, lm)
        val i1 = m.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(mark)
        val i2 = m.mostAbstractInitialAp(AccessPathBase.Return).prependAccessor(mark)
        val initial = setOf(i1, i2)
        val final = m.finalFact(AccessPathBase.ClassStatic, mark)

        assertNotNull(set.add(inst, initial, final))
        assertNull(set.add(inst, initial, final))
    }

    @Test
    fun `nd f2f canonicalizes initial exclusions before key publication`() {
        val m = mkManager()
        val set = m.methodEdgesNDInitialToFinalApSet(inst, 0, lm)
        val concrete = ExclusionSet.Concrete(TaintMarkAccessor("excluded"))
        val supplied = setOf(m.mostAbstractInitialAp(AccessPathBase.This).replaceExclusions(concrete))
        val canonical = supplied.mapTo(hashSetOf()) { it.replaceExclusions(ExclusionSet.Universe) }
        val final = m.finalFact(AccessPathBase.ClassStatic, mark)

        val added = assertNotNull(set.add(inst, supplied, final))
        assertEquals(canonical, added.first)
        assertNull(set.add(inst, canonical, final), "equivalent canonical key is idempotent")

        val found = mutableListOf<FinalFactAp>()
        set.collectApAtStatement(found, inst, canonical, m.mostAbstractInitialAp(AccessPathBase.ClassStatic))
        assertEquals(1, found.size)
    }

    @Test
    fun `final fact list rejects transient collapsed access without shifting its arrays`() {
        val m = mkManager()
        val list = m.finalFactList()
        val collapsed = BaseOnlyFinalFactAp(
            m,
            AccessPathBase.This,
            packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, COLLAPSED_MARK),
            ExclusionSet.Empty,
        )
        list.add(collapsed)

        val valid = m.finalFact(AccessPathBase.Return, mark)
        list.add(valid)
        assertEquals(valid, list.get(0))
        assertFailsWith<IndexOutOfBoundsException> { list.get(1) }
        assertEquals(valid, list.removeLast())
        assertFailsWith<NoSuchElementException> { list.removeLast() }
    }
}
