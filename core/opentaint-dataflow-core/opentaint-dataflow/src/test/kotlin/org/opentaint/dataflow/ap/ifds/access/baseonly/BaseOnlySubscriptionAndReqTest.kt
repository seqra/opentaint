package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.SideEffectSummary
import org.opentaint.dataflow.ap.ifds.SummaryEdgeStorageWithSubscribers
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.FactEdgeSummarySubscription
import org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.FactNDEdgeSummarySubscription
import org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.ZeroEdgeSummarySubscription
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class BaseOnlySubscriptionAndReqTest {
    private val manager = BaseOnlyApManager(
        AnyAccessorUnrollStrategy.AnyAccessorDisabled,
        Cancellation(),
        fieldSensitive = true,
    )
    private val fieldA = FieldAccessor("Owner", "a", "Value")
    private val fieldB = FieldAccessor("Owner", "b", "Value")
    private val mark = TaintMarkAccessor("m")
    private val entryPoint by lazy { MethodEntryPoint(EmptyMethodContext, inst) }

    private val method = object : CommonMethod {
        override val name: String = "baseOnlySubscription"
        override val parameters: List<CommonMethodParameter> = listOf(object : CommonMethodParameter {
            override val type: CommonTypeName = object : CommonTypeName {
                override val typeName: String = "java.lang.Object"
            }
        })
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
            override val method: CommonMethod get() = this@BaseOnlySubscriptionAndReqTest.method
        }
    }

    private fun pattern(field: FieldAccessor): BaseOnlyAccess =
        packBaseOnlyAccess(NO_ACCESSOR, manager.interner.index(field), ABSTRACT_MARK)

    private fun marked(field: FieldAccessor): BaseOnlyAccess =
        packBaseOnlyAccess(NO_ACCESSOR, manager.interner.index(field), manager.interner.index(mark))

    private fun initial(
        access: BaseOnlyAccess,
        base: AccessPathBase = AccessPathBase.This,
    ): BaseOnlyInitialFactAp = BaseOnlyInitialFactAp(manager, base, access, ExclusionSet.Empty)

    private fun final(
        access: BaseOnlyAccess,
        base: AccessPathBase = AccessPathBase.Return,
    ): BaseOnlyFinalFactAp = BaseOnlyFinalFactAp(manager, base, access, ExclusionSet.Universe)

    @Test
    fun `summary storage publishes only non-empty deltas`() {
        val storage = SummaryEdgeStorageWithSubscribers(manager, entryPoint)
        val summaryDeltas = mutableListOf<List<Edge>>()
        val requirementDeltas = mutableListOf<List<InitialFactAp>>()
        val sideEffectDeltas = mutableListOf<List<SideEffectSummary>>()
        storage.subscribeOnEdges(object : SummaryEdgeStorageWithSubscribers.Subscriber {
            override fun newSummaryEdges(edges: List<Edge>) {
                summaryDeltas.add(edges)
            }

            override fun newSideEffectRequirement(
                methodEntryPoint: MethodEntryPoint,
                requirements: List<InitialFactAp>,
            ) {
                requirementDeltas.add(requirements)
            }

            override fun newSideEffectSummaries(
                methodEntryPoint: MethodEntryPoint,
                sideEffects: List<SideEffectSummary>,
            ) {
                sideEffectDeltas.add(sideEffects)
            }
        })

        storage.addEdges(emptyList())
        storage.sideEffectRequirement(emptyList())
        storage.addSideEffectSummaries(emptyList())
        assertTrue(summaryDeltas.isEmpty())
        assertTrue(requirementDeltas.isEmpty())
        assertTrue(sideEffectDeltas.isEmpty())

        val edge = Edge.FactToFact(
            entryPoint,
            initial(pattern(fieldA)),
            inst,
            BaseOnlyFinalFactAp(manager, AccessPathBase.Return, marked(fieldA), ExclusionSet.Empty),
        )
        storage.addEdges(listOf(edge))
        assertEquals(1, summaryDeltas.size)
        assertEquals(1, requirementDeltas.size)

        storage.addEdges(listOf(edge))
        assertEquals(1, summaryDeltas.size, "a subsumed edge has no publication delta")
        assertEquals(1, requirementDeltas.size, "a subsumed requirement has no publication delta")

        val sideEffect = SideEffectSummary.ZeroSideEffectSummary(object : SideEffectKind {})
        storage.addSideEffectSummaries(listOf(sideEffect))
        assertEquals(1, sideEffectDeltas.size)

        storage.addSideEffectSummaries(listOf(sideEffect))
        assertEquals(1, sideEffectDeltas.size, "a duplicate side effect has no publication delta")
    }

    @Test
    fun `fact subscription indexes applicable and empty delta candidates`() {
        val sub = manager.accessPathSubscription()
        val callerInitial = initial(pattern(fieldA))
        val exactExit = final(pattern(fieldA))
        val extendedExit = final(marked(fieldA))
        val unrelatedExit = final(marked(fieldB))

        assertNotNull(sub.addFactToFact(inst, AccessPathBase.This, callerInitial, exactExit))
        assertNotNull(sub.addFactToFact(inst, AccessPathBase.This, callerInitial, extendedExit))
        assertNotNull(sub.addFactToFact(inst, AccessPathBase.This, callerInitial, unrelatedExit))
        assertNull(sub.addFactToFact(inst, AccessPathBase.This, callerInitial, extendedExit))

        val summaryInitial = initial(pattern(fieldA))
        val applicable = mutableListOf<FactEdgeSummarySubscription>()
        sub.collectFactEdge(applicable, summaryInitial, emptyDeltaRequired = false)
        assertEquals(2, applicable.size, "identity and non-empty delta candidates are applicable")

        val empty = mutableListOf<FactEdgeSummarySubscription>()
        sub.collectFactEdge(empty, summaryInitial, emptyDeltaRequired = true)
        assertEquals(2, empty.size, "empty-delta mode uses the same conservative candidates")
    }

    @Test
    fun `fact subscription preserves exclusion-distinct registrations`() {
        val sub = manager.accessPathSubscription()
        val access = pattern(fieldA)
        val exit = final(marked(fieldA))
        val first = initial(access).replaceExclusions(ExclusionSet.Empty.add(fieldA))
        val expanded = first.replaceExclusions(first.exclusions.add(fieldB))

        assertNotNull(sub.addFactToFact(inst, AccessPathBase.This, first, exit))
        assertNotNull(sub.addFactToFact(inst, AccessPathBase.This, expanded, exit))
        assertNull(sub.addFactToFact(inst, AccessPathBase.This, first, exit))

        val collected = mutableListOf<FactEdgeSummarySubscription>()
        sub.collectFactEdge(collected, initial(access), emptyDeltaRequired = false)

        val retained = collected.map { it.setStatements(entryPoint, inst).callerPathEdge }.toSet()
        assertEquals(setOf(first, expanded), retained.mapTo(hashSetOf()) { it.initialFactAp })
        assertEquals(setOf(first.exclusions, expanded.exclusions), retained.mapTo(hashSetOf()) { it.factAp.exclusions })
    }

    @Test
    fun `zero subscription indexes applicable candidates`() {
        val sub = manager.accessPathSubscription()
        sub.addZeroToFact(inst, AccessPathBase.This, final(pattern(fieldA)))
        sub.addZeroToFact(inst, AccessPathBase.This, final(marked(fieldA)))
        sub.addZeroToFact(inst, AccessPathBase.This, final(marked(fieldB)))

        val collected = mutableListOf<ZeroEdgeSummarySubscription>()
        sub.collectZeroEdge(collected, initial(pattern(fieldA)))
        assertEquals(2, collected.size, "identity and non-empty delta candidates are applicable")
    }

    @Test
    fun `ND subscription indexes applicable candidates for both residual modes`() {
        val sub = manager.accessPathSubscription()
        val callerInitial = setOf(
            initial(pattern(fieldA)).replaceExclusions(ExclusionSet.Universe),
            initial(pattern(fieldB), AccessPathBase.Argument(0)).replaceExclusions(ExclusionSet.Universe),
        )
        sub.addNDFactToFact(inst, AccessPathBase.This, callerInitial, final(pattern(fieldA)))
        sub.addNDFactToFact(inst, AccessPathBase.This, callerInitial, final(marked(fieldA)))
        sub.addNDFactToFact(inst, AccessPathBase.This, callerInitial, final(marked(fieldB)))

        val nonEmpty = mutableListOf<FactNDEdgeSummarySubscription>()
        sub.collectFactNDEdge(nonEmpty, initial(pattern(fieldA)), emptyDeltaRequired = false)
        assertEquals(2, nonEmpty.size)

        val empty = mutableListOf<FactNDEdgeSummarySubscription>()
        sub.collectFactNDEdge(empty, initial(pattern(fieldA)), emptyDeltaRequired = true)
        assertEquals(2, empty.size)
    }

    @Test
    fun `ND subscription normalizes caller initial exclusions to Universe`() {
        val sub = manager.accessPathSubscription()
        val access = pattern(fieldA)
        val emptyInitial = setOf(initial(access))
        val universeInitial = setOf(initial(access).replaceExclusions(ExclusionSet.Universe))
        val exit = final(marked(fieldA))

        assertNotNull(sub.addNDFactToFact(inst, AccessPathBase.This, emptyInitial, exit))
        assertNull(
            sub.addNDFactToFact(inst, AccessPathBase.This, universeInitial, exit),
            "exclusions are not part of an ND subscription identity",
        )

        val collected = mutableListOf<FactNDEdgeSummarySubscription>()
        sub.collectFactNDEdge(collected, initial(access), emptyDeltaRequired = false)
        assertEquals(1, collected.size)
    }

    @Test
    fun `fact subscription index equals BaseOnly delta scan`() {
        val exits = listOf(
            pattern(fieldA),
            marked(fieldA),
            marked(fieldB),
            packBaseOnlyAccess(NO_ACCESSOR, manager.interner.index(fieldA), manager.finalAccessorAccess.suffixIdx),
        )
        val summaryAccess = pattern(fieldA)
        val callerInitial = initial(pattern(fieldA))
        val ndInitial = setOf(
            callerInitial.replaceExclusions(ExclusionSet.Universe),
            initial(pattern(fieldB), AccessPathBase.Argument(0)).replaceExclusions(ExclusionSet.Universe),
        )
        val sub = manager.accessPathSubscription()
        exits.forEach { exit ->
            sub.addFactToFact(inst, AccessPathBase.This, callerInitial, final(exit))
            sub.addNDFactToFact(inst, AccessPathBase.This, ndInitial, final(exit))
        }

        val applicable = mutableListOf<FactEdgeSummarySubscription>()
        sub.collectFactEdge(applicable, initial(summaryAccess), emptyDeltaRequired = false)
        val expectedApplicable = exits.count { exit ->
            val match = BaseOnlyAccessOps.matchPrefix(exit, summaryAccess)
            match.emptyDelta || match.hasSuffix
        }
        assertEquals(expectedApplicable, applicable.size)

        val empty = mutableListOf<FactEdgeSummarySubscription>()
        sub.collectFactEdge(empty, initial(summaryAccess), emptyDeltaRequired = true)
        assertEquals(expectedApplicable, empty.size)

        val ndResult = mutableListOf<FactNDEdgeSummarySubscription>()
        sub.collectFactNDEdge(ndResult, initial(summaryAccess), emptyDeltaRequired = false)
        assertEquals(expectedApplicable, ndResult.size)
    }

    @Test
    fun `fact subscription index equals matchPrefix for all canonical shapes`() {
        val static = manager.interner.index(ClassStaticAccessor("Owner"))
        val fieldAIdx = manager.interner.index(fieldA)
        val fieldBIdx = manager.interner.index(fieldB)
        val markIdx = manager.interner.index(mark)
        val accesses = listOf(
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0),
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1),
            BaseOnlyAccessOps.abstractAt(static, NO_ACCESSOR, 1),
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 2),
            BaseOnlyAccessOps.abstractAt(static, NO_ACCESSOR, 2),
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, fieldAIdx, 2),
            packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, markIdx),
            packBaseOnlyAccess(NO_ACCESSOR, fieldAIdx, markIdx),
            packBaseOnlyAccess(NO_ACCESSOR, fieldBIdx, markIdx),
            packBaseOnlyAccess(static, NO_ACCESSOR, markIdx),
            packBaseOnlyAccess(static, fieldAIdx, markIdx),
        )
        val sub = manager.accessPathSubscription()
        val callerInitial = initial(pattern(fieldA))
        accesses.forEach { exit ->
            assertNotNull(sub.addFactToFact(inst, AccessPathBase.This, callerInitial, final(exit)))
        }

        accesses.forEach { summaryAccess ->
            val applicable = mutableListOf<FactEdgeSummarySubscription>()
            sub.collectFactEdge(applicable, initial(summaryAccess), emptyDeltaRequired = false)
            val expectedApplicable = accesses.count { exit ->
                BaseOnlyAccessOps.matchPrefix(exit, summaryAccess).let { it.emptyDelta || it.hasSuffix }
            }
            assertEquals(expectedApplicable, applicable.size, "applicable lookup for $summaryAccess")

            val empty = mutableListOf<FactEdgeSummarySubscription>()
            sub.collectFactEdge(empty, initial(summaryAccess), emptyDeltaRequired = true)
            assertEquals(
                expectedApplicable,
                empty.size,
                "empty-delta mode uses the same conservative candidates for $summaryAccess",
            )
        }
    }

    @Test
    fun `zero subscription index equals matchPrefix for all canonical shapes`() {
        val static = manager.interner.index(ClassStaticAccessor("Owner"))
        val fieldAIdx = manager.interner.index(fieldA)
        val fieldBIdx = manager.interner.index(fieldB)
        val markIdx = manager.interner.index(mark)
        val accesses = listOf(
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0),
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1),
            BaseOnlyAccessOps.abstractAt(static, NO_ACCESSOR, 1),
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 2),
            BaseOnlyAccessOps.abstractAt(static, NO_ACCESSOR, 2),
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, fieldAIdx, 2),
            packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, markIdx),
            packBaseOnlyAccess(NO_ACCESSOR, fieldAIdx, markIdx),
            packBaseOnlyAccess(NO_ACCESSOR, fieldBIdx, markIdx),
            packBaseOnlyAccess(static, NO_ACCESSOR, markIdx),
            packBaseOnlyAccess(static, fieldAIdx, markIdx),
        )
        val sub = manager.accessPathSubscription()
        accesses.forEach { exit ->
            assertNotNull(
                sub.addZeroToFact(
                    inst,
                    AccessPathBase.ClassStatic,
                    final(exit, AccessPathBase.ClassStatic),
                )
            )
        }

        accesses.forEach { summaryAccess ->
            val actual = mutableListOf<ZeroEdgeSummarySubscription>()
            sub.collectZeroEdge(actual, initial(summaryAccess, AccessPathBase.ClassStatic))
            val expected = accesses.count { exit ->
                BaseOnlyAccessOps.matchPrefix(exit, summaryAccess).let { it.emptyDelta || it.hasSuffix }
            }
            assertEquals(expected, actual.size, "applicable lookup for $summaryAccess")
        }
    }

    @Test
    fun `side effect requirement filters same-base entries by overlap`() {
        val storage = manager.sideEffectRequirementApStorage()
        val requirementA = initial(pattern(fieldA))
        val requirementB = initial(pattern(fieldB))

        assertEquals(2, storage.add(listOf(requirementA, requirementB)).size)
        assertTrue(storage.add(listOf(requirementA)).isEmpty(), "same requirement is subsumed")

        val matching = mutableListOf<InitialFactAp>()
        storage.filterTo(matching, final(marked(fieldA), AccessPathBase.This))
        assertEquals(
            listOf<InitialFactAp>(requirementA),
            matching,
            "same-base field-B requirement must not be broadcast",
        )

        val otherBase = mutableListOf<InitialFactAp>()
        storage.filterTo(otherBase, final(marked(fieldA), AccessPathBase.Return))
        assertTrue(otherBase.isEmpty(), "no requirement exists for the unrelated base")

        val all = mutableListOf<InitialFactAp>()
        storage.collectAllRequirementsTo(all)
        assertEquals(setOf<InitialFactAp>(requirementA, requirementB), all.toSet())
    }


    @Test
    fun `side effect requirement publishes exclusion delta and retains the union`() {
        val storage = manager.sideEffectRequirementApStorage()
        val access = pattern(fieldA)
        val first = BaseOnlyInitialFactAp(
            manager,
            AccessPathBase.This,
            access,
            ExclusionSet.Empty.add(fieldA),
        )
        val expanded = first.replaceExclusions(first.exclusions.add(fieldB))

        assertEquals(listOf<InitialFactAp>(first), storage.add(listOf(first)))

        val delta = storage.add(listOf(expanded))
        assertEquals(1, delta.size)
        assertEquals(ExclusionSet.Empty.add(fieldB), delta.single().exclusions)

        val retained = mutableListOf<InitialFactAp>()
        storage.collectAllRequirementsTo(retained)
        assertEquals(listOf(expanded), retained)
    }

    @Test
    fun `side effect requirement filtering equals a scan reference`() {
        val storage = manager.sideEffectRequirementApStorage()
        val requirements = listOf(
            initial(pattern(fieldA)),
            initial(pattern(fieldB)),
            initial(ABSTRACT_EMPTY_ACCESS),
        )
        storage.add(requirements)

        val facts = listOf(marked(fieldA), marked(fieldB), pattern(fieldA), pattern(fieldB))
        for (factAccess in facts) {
            val expected = requirements.filter {
                baseOnlySummaryInitialMatches(factAccess, (it as BaseOnlyInitialFactAp).access)
            }.toSet()
            val actual = mutableListOf<InitialFactAp>()
            storage.filterTo(actual, final(factAccess, AccessPathBase.This))
            assertEquals(expected, actual.toSet(), "scan reference for ${manager.renderAccess(factAccess)}")
        }
    }

    @Test
    fun `subscription filtering covers the corresponding Tree scenario`() {
        val treeManager = TreeApManager(
            AnyAccessorUnrollStrategy.AnyAccessorDisabled,
            RefManager(),
            Cancellation(),
        )
        val treeSub = treeManager.accessPathSubscription()
        val baseOnlySub = manager.accessPathSubscription()

        val treeCallerInitial = treeManager.abstractInitialOf(AccessPathBase.Argument(0), fieldA)
        val baseOnlyCallerInitial = manager.abstractInitialOf(AccessPathBase.Argument(0), fieldA)
        treeSub.addFactToFact(
            inst,
            AccessPathBase.This,
            treeCallerInitial,
            treeManager.finalOf(AccessPathBase.Return, fieldA, mark),
        )
        treeSub.addFactToFact(
            inst,
            AccessPathBase.This,
            treeCallerInitial,
            treeManager.finalOf(AccessPathBase.Return, fieldB, mark),
        )
        baseOnlySub.addFactToFact(
            inst,
            AccessPathBase.This,
            baseOnlyCallerInitial,
            manager.finalOf(AccessPathBase.Return, fieldA, mark),
        )
        baseOnlySub.addFactToFact(
            inst,
            AccessPathBase.This,
            baseOnlyCallerInitial,
            manager.finalOf(AccessPathBase.Return, fieldB, mark),
        )

        val treeResult = mutableListOf<FactEdgeSummarySubscription>()
        treeSub.collectFactEdge(
            treeResult,
            treeManager.abstractInitialOf(AccessPathBase.This, fieldA),
            emptyDeltaRequired = false,
        )
        val baseOnlyResult = mutableListOf<FactEdgeSummarySubscription>()
        baseOnlySub.collectFactEdge(
            baseOnlyResult,
            manager.abstractInitialOf(AccessPathBase.This, fieldA),
            emptyDeltaRequired = false,
        )

        assertEquals(1, treeResult.size, "Tree scenario must select only field A")
        assertTrue(baseOnlyResult.size >= treeResult.size, "BaseOnly dropped a Tree subscription match")
    }

    private fun ApManager.abstractInitialOf(base: AccessPathBase, vararg accessors: Accessor): InitialFactAp {
        var fact = mostAbstractInitialAp(base)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun ApManager.finalOf(base: AccessPathBase, vararg accessors: Accessor): FinalFactAp {
        var fact = createFinalAp(base, ExclusionSet.Universe)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }
}
