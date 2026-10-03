package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.SideEffectSummary.FactSideEffectSummary
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.ReadableAccessorList
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.ap.ifds.serialization.MethodContextSerializer
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

/** Bounded, public-API differential scenarios for every BaseOnly storage family. */
class BaseOnlyTreeDifferentialStorageTest {
    private val fieldA = FieldAccessor("Owner", "a", "Value")
    private val fieldB = FieldAccessor("Owner", "b", "Value")
    private val mark = TaintMarkAccessor("source")
    private val exA = ExclusionSet.Concrete(TaintMarkAccessor("excluded-a"))
    private val exB = ExclusionSet.Concrete(TaintMarkAccessor("excluded-b"))
    private val kind = object : SideEffectKind {}
    private val entryPoint = MethodEntryPoint(EmptyMethodContext, inst)

    private fun managers(): Pair<TreeApManager, BaseOnlyApManager> =
        TreeApManager(
            AnyAccessorUnrollStrategy.AnyAccessorDisabled,
            RefManager(),
            Cancellation(),
        ) to BaseOnlyApManager(
            AnyAccessorUnrollStrategy.AnyAccessorDisabled,
            Cancellation(),
            fieldSensitive = true,
            summaryStorageFieldGeneralizationEnabled = true,
        )

    @Test
    fun `intraprocedural Z2F F2F and ND sets cover Tree collection and deltas`() {
        val (tree, baseOnly) = managers()
        val treeZ2F = tree.methodEdgesFinalApSet(inst, 0, languageManager)
        val baseOnlyZ2F = baseOnly.methodEdgesFinalApSet(inst, 0, languageManager)
        val treeFinals = listOf(tree.finalOf(AccessPathBase.Return, fieldA, mark), tree.finalOf(AccessPathBase.Return, fieldB, mark))
        val baseOnlyFinals = listOf(baseOnly.finalOf(AccessPathBase.Return, fieldA, mark), baseOnly.finalOf(AccessPathBase.Return, fieldB, mark))

        treeFinals.forEach { assertNotNull(treeZ2F.add(inst, it)) }
        baseOnlyFinals.forEach { assertNotNull(baseOnlyZ2F.add(inst, it)) }
        assertNull(treeZ2F.add(inst, treeFinals.first()))
        assertNull(baseOnlyZ2F.add(inst, baseOnlyFinals.first()))
        assertFinalCollectionCoversTree(
            collectFinals { treeZ2F.collectApAtStatement(it, inst) },
            collectFinals { baseOnlyZ2F.collectApAtStatement(it, inst) },
            "intraprocedural Z2F collect-all",
        )

        val treeInitial = tree.initialOf(AccessPathBase.This, exA, fieldA)
        val baseOnlyInitial = baseOnly.initialOf(AccessPathBase.This, exA, fieldA)
        val treeF2F = tree.methodEdgesInitialToFinalApSet(inst, 0, languageManager)
        val baseOnlyF2F = baseOnly.methodEdgesInitialToFinalApSet(inst, 0, languageManager)
        treeFinals.forEach { assertTrue(treeF2F.add(inst, treeInitial, it.replaceExclusions(exA)).isNotEmpty()) }
        baseOnlyFinals.forEach { assertTrue(baseOnlyF2F.add(inst, baseOnlyInitial, it.replaceExclusions(exA)).isNotEmpty()) }
        assertTrue(treeF2F.add(inst, treeInitial, treeFinals.first().replaceExclusions(exA)).isEmpty())
        assertTrue(baseOnlyF2F.add(inst, baseOnlyInitial, baseOnlyFinals.first().replaceExclusions(exA)).isEmpty())

        val treeF2FAll = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        val baseOnlyF2FAll = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        treeF2F.collectApAtStatement(treeF2FAll, inst)
        baseOnlyF2F.collectApAtStatement(baseOnlyF2FAll, inst)
        assertFinalCollectionCoversTree(treeF2FAll.map { it.second }, baseOnlyF2FAll.map { it.second }, "intraprocedural F2F collect-all")
        assertTrue(baseOnlyF2FAll.all { it.second.exclusions == exA })

        val treeF2FExact = mutableListOf<FinalFactAp>()
        val baseOnlyF2FExact = mutableListOf<FinalFactAp>()
        treeF2F.collectApAtStatement(treeF2FExact, inst, treeInitial, tree.mostAbstractInitialAp(AccessPathBase.Return))
        baseOnlyF2F.collectApAtStatement(baseOnlyF2FExact, inst, baseOnlyInitial, baseOnly.mostAbstractInitialAp(AccessPathBase.Return))
        assertFinalCollectionCoversTree(treeF2FExact, baseOnlyF2FExact, "intraprocedural F2F exact-initial")

        val treeNdInitial = setOf(
            tree.initialOf(AccessPathBase.This, ExclusionSet.Universe, fieldA),
            tree.initialOf(AccessPathBase.Exception, ExclusionSet.Universe, fieldB),
        )
        val baseOnlyNdInitial = setOf(
            baseOnly.initialOf(AccessPathBase.This, ExclusionSet.Universe, fieldA),
            baseOnly.initialOf(AccessPathBase.Exception, ExclusionSet.Universe, fieldB),
        )
        val treeND = tree.methodEdgesNDInitialToFinalApSet(inst, 0, languageManager)
        val baseOnlyND = baseOnly.methodEdgesNDInitialToFinalApSet(inst, 0, languageManager)
        treeFinals.forEach { assertNotNull(treeND.add(inst, treeNdInitial, it.replaceExclusions(ExclusionSet.Universe))) }
        baseOnlyFinals.forEach { assertNotNull(baseOnlyND.add(inst, baseOnlyNdInitial, it.replaceExclusions(ExclusionSet.Universe))) }
        assertNull(treeND.add(inst, treeNdInitial, treeFinals.first().replaceExclusions(ExclusionSet.Universe)))
        assertNull(baseOnlyND.add(inst, baseOnlyNdInitial, baseOnlyFinals.first().replaceExclusions(ExclusionSet.Universe)))

        val treeNDAll = mutableListOf<Pair<Set<InitialFactAp>, FinalFactAp>>()
        val baseOnlyNDAll = mutableListOf<Pair<Set<InitialFactAp>, FinalFactAp>>()
        treeND.collectApAtStatement(treeNDAll, inst)
        baseOnlyND.collectApAtStatement(baseOnlyNDAll, inst)
        assertFinalCollectionCoversTree(treeNDAll.map { it.second }, baseOnlyNDAll.map { it.second }, "intraprocedural ND collect-all")
        val treeNDExact = mutableListOf<FinalFactAp>()
        val baseOnlyNDExact = mutableListOf<FinalFactAp>()
        treeND.collectApAtStatement(treeNDExact, inst, treeNdInitial, tree.mostAbstractInitialAp(AccessPathBase.Return))
        baseOnlyND.collectApAtStatement(baseOnlyNDExact, inst, baseOnlyNdInitial, baseOnly.mostAbstractInitialAp(AccessPathBase.Return))
        assertFinalCollectionCoversTree(treeNDExact, baseOnlyNDExact, "intraprocedural ND exact-initial")
    }

    @Test
    fun `method Z2F F2F and ND summary queries cover Tree`() {
        val (tree, baseOnly) = managers()
        val treeFinals = listOf(tree.finalOf(AccessPathBase.Return, fieldA, mark), tree.finalOf(AccessPathBase.Return, fieldB, mark))
        val baseOnlyFinals = listOf(baseOnly.finalOf(AccessPathBase.Return, fieldA, mark), baseOnly.finalOf(AccessPathBase.Return, fieldB, mark))

        val treeZ2F = tree.methodFinalApSummariesStorage(inst)
        val baseOnlyZ2F = baseOnly.methodFinalApSummariesStorage(inst)
        val treeZeroEdges = treeFinals.map { Edge.ZeroToFact(entryPoint, inst, it.replaceExclusions(ExclusionSet.Universe)) }
        val baseOnlyZeroEdges = baseOnlyFinals.map { Edge.ZeroToFact(entryPoint, inst, it.replaceExclusions(ExclusionSet.Universe)) }
        treeZ2F.add(treeZeroEdges, mutableListOf())
        baseOnlyZ2F.add(baseOnlyZeroEdges, mutableListOf())
        val treeZeroBuilders = mutableListOf<org.opentaint.dataflow.ap.ifds.ZeroToFactEdgeBuilder>()
        val baseOnlyZeroBuilders = mutableListOf<org.opentaint.dataflow.ap.ifds.ZeroToFactEdgeBuilder>()
        treeZ2F.filterEdgesTo(treeZeroBuilders, AccessPathBase.Return)
        baseOnlyZ2F.filterEdgesTo(baseOnlyZeroBuilders, AccessPathBase.Return)
        assertFinalCollectionCoversTree(
            treeZeroBuilders.map { it.setEntryPoint(entryPoint).setExitStatement(inst).build().factAp },
            baseOnlyZeroBuilders.map { it.setEntryPoint(entryPoint).setExitStatement(inst).build().factAp },
            "method Z2F",
        )

        val treeInitial = tree.initialOf(AccessPathBase.This, exA, fieldA)
        val baseOnlyInitial = baseOnly.initialOf(AccessPathBase.This, exA, fieldA)
        val treeF2F = tree.methodInitialToFinalApSummariesStorage(inst)
        val baseOnlyF2F = baseOnly.methodInitialToFinalApSummariesStorage(inst)
        treeF2F.add(treeFinals.map { Edge.FactToFact(entryPoint, treeInitial, inst, it.replaceExclusions(exA)) }, mutableListOf())
        baseOnlyF2F.add(baseOnlyFinals.map { Edge.FactToFact(entryPoint, baseOnlyInitial, inst, it.replaceExclusions(exA)) }, mutableListOf())
        val treeF2FBuilders = mutableListOf<org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder>()
        val baseOnlyF2FBuilders = mutableListOf<org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder>()
        treeF2F.filterEdgesTo(treeF2FBuilders, tree.finalOf(AccessPathBase.This, fieldA), AccessPathBase.Return)
        baseOnlyF2F.filterEdgesTo(baseOnlyF2FBuilders, baseOnly.finalOf(AccessPathBase.This, fieldA), AccessPathBase.Return)
        val treeF2FFacts = treeF2FBuilders.map { it.setEntryPoint(entryPoint).setExitStatement(inst).build().factAp }
        val baseOnlyF2FFacts = baseOnlyF2FBuilders.map { it.setEntryPoint(entryPoint).setExitStatement(inst).build().factAp }
        assertFinalCollectionCoversTree(treeF2FFacts, baseOnlyF2FFacts, "method F2F patterned")

        val treeNdInitial = setOf(
            tree.initialOf(AccessPathBase.This, ExclusionSet.Universe, fieldA),
            tree.initialOf(AccessPathBase.Exception, ExclusionSet.Universe, fieldB),
        )
        val baseOnlyNdInitial = setOf(
            baseOnly.initialOf(AccessPathBase.This, ExclusionSet.Universe, fieldA),
            baseOnly.initialOf(AccessPathBase.Exception, ExclusionSet.Universe, fieldB),
        )
        val treeND = tree.methodNDInitialToFinalApSummariesStorage(inst)
        val baseOnlyND = baseOnly.methodNDInitialToFinalApSummariesStorage(inst)
        treeND.add(treeFinals.map { Edge.NDFactToFact(entryPoint, treeNdInitial, inst, it.replaceExclusions(ExclusionSet.Universe)) }, mutableListOf())
        baseOnlyND.add(baseOnlyFinals.map { Edge.NDFactToFact(entryPoint, baseOnlyNdInitial, inst, it.replaceExclusions(ExclusionSet.Universe)) }, mutableListOf())
        val treeNDBuilders = mutableListOf<org.opentaint.dataflow.ap.ifds.NDFactToFactEdgeBuilder>()
        val baseOnlyNDBuilders = mutableListOf<org.opentaint.dataflow.ap.ifds.NDFactToFactEdgeBuilder>()
        treeND.filterEdgesTo(treeNDBuilders, tree.mostAbstractFinalAp(AccessPathBase.This), AccessPathBase.Return)
        baseOnlyND.filterEdgesTo(baseOnlyNDBuilders, baseOnly.mostAbstractFinalAp(AccessPathBase.This), AccessPathBase.Return)
        assertFinalCollectionCoversTree(
            treeNDBuilders.map { it.setEntryPoint(entryPoint).setExitStatement(inst).build().factAp },
            baseOnlyNDBuilders.map { it.setEntryPoint(entryPoint).setExitStatement(inst).build().factAp },
            "method ND patterned",
        )
    }

    @Test
    fun `method ND summary query does not enumerate a different concrete static accessor`() {
        val (_, baseOnly) = managers()
        val staticA = ClassStaticAccessor("StaticA")
        val staticB = ClassStaticAccessor("StaticB")
        val storage = baseOnly.methodNDInitialToFinalApSummariesStorage(inst)
        val initialA = setOf(
            baseOnly.initialOf(AccessPathBase.ClassStatic, ExclusionSet.Universe, staticA, mark),
            baseOnly.initialOf(AccessPathBase.This, ExclusionSet.Universe, fieldA),
        )
        val initialB = setOf(
            baseOnly.initialOf(AccessPathBase.ClassStatic, ExclusionSet.Universe, staticB, mark),
            baseOnly.initialOf(AccessPathBase.Exception, ExclusionSet.Universe, fieldB),
        )
        storage.add(
            listOf(
                Edge.NDFactToFact(
                    entryPoint,
                    initialA,
                    inst,
                    baseOnly.finalOf(AccessPathBase.Return, ExclusionSet.Universe, fieldA, mark),
                ),
                Edge.NDFactToFact(
                    entryPoint,
                    initialB,
                    inst,
                    baseOnly.finalOf(AccessPathBase.Return, ExclusionSet.Universe, fieldB, mark),
                ),
            ),
            mutableListOf(),
        )

        val selected = mutableListOf<org.opentaint.dataflow.ap.ifds.NDFactToFactEdgeBuilder>()
        storage.filterEdgesTo(
            selected,
            baseOnly.finalOf(AccessPathBase.ClassStatic, staticA, mark),
            AccessPathBase.Return,
        )

        assertEquals(1, selected.size)
        assertEquals(
            initialA,
            selected.single().setEntryPoint(entryPoint).setExitStatement(inst).build().initialFacts,
        )
    }

    @Test
    fun `generalized F2F summaries cover every Tree member application`() {
        val (tree, baseOnly) = managers()
        val fields = (0..MAX_FIELD_ENUMERATION_EDGES).map { index ->
            FieldAccessor("Owner", "generalized-$index", "Value")
        }
        val marks = fields.indices.map { index -> TaintMarkAccessor("generalized-mark-$index") }
        val treeStorage = tree.methodInitialToFinalApSummariesStorage(inst)
        val baseOnlyStorage = baseOnly.methodInitialToFinalApSummariesStorage(inst)

        treeStorage.add(
            fields.mapIndexed { index, field ->
                Edge.FactToFact(
                    entryPoint,
                    tree.initialOf(
                        AccessPathBase.This,
                        if (index == 0) exA else ExclusionSet.Empty,
                        field,
                    ),
                    inst,
                    tree.abstractFinalOf(AccessPathBase.Return, fields.reversed()[index])
                        .replaceExclusions(if (index == 0) exA else ExclusionSet.Empty),
                )
            },
            mutableListOf(),
        )
        baseOnlyStorage.add(
            fields.mapIndexed { index, field ->
                Edge.FactToFact(
                    entryPoint,
                    baseOnly.initialOf(
                        AccessPathBase.This,
                        if (index == 0) exA else ExclusionSet.Empty,
                        field,
                    ),
                    inst,
                    baseOnly.abstractFinalOf(AccessPathBase.Return, fields.reversed()[index])
                        .replaceExclusions(if (index == 0) exA else ExclusionSet.Empty),
                )
            },
            mutableListOf(),
        )

        val baseOnlyStored = mutableListOf<org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder>()
        baseOnlyStorage.filterEdgesTo(
            baseOnlyStored,
            initialFactPattern = null,
            finalFactBase = AccessPathBase.Return,
        )
        assertEquals(1, baseOnlyStored.size, "the eligible field family must be generalized")

        fields.forEachIndexed { index, field ->
            val treeSelected = mutableListOf<org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder>()
            val baseOnlySelected = mutableListOf<org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder>()
            treeStorage.filterEdgesTo(
                treeSelected,
                tree.finalOf(AccessPathBase.This, field, marks[index]),
                AccessPathBase.Return,
            )
            baseOnlyStorage.filterEdgesTo(
                baseOnlySelected,
                baseOnly.finalOf(AccessPathBase.This, field, marks[index]),
                AccessPathBase.Return,
            )

            assertTrue(treeSelected.isNotEmpty(), "Tree member $index must be applicable")
            assertTrue(baseOnlySelected.isNotEmpty(), "generalization lost Tree member $index")
            val input = baseOnly.finalOf(AccessPathBase.This, field, marks[index])
            val applied = baseOnlySelected.flatMap { builder ->
                val summary = builder
                    .setEntryPoint(entryPoint)
                    .setExitStatement(inst)
                    .build()
                MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge(
                    input,
                    summary.initialFactAp,
                ).mapNotNull { effect ->
                    when (effect) {
                        is SummaryEdgeApplication.SummaryApRefinement ->
                            summary.factAp
                                .concat(FactTypeChecker.Dummy, effect.delta)
                                ?.replaceExclusions(input.exclusions)

                        is SummaryEdgeApplication.SummaryExclusionRefinement ->
                            summary.factAp.replaceExclusions(effect.exclusion)
                    }
                }
            }
            val expected = baseOnly.exactInitialOf(
                AccessPathBase.Return,
                fields.reversed()[index],
                marks[index],
            )
            assertTrue(
                applied.any { it.contains(expected) },
                "applying the generalized summary does not cover Tree member $index: $applied",
            )
        }
    }

    @Test
    fun `field generalization keeps concrete field mark mappings exact`() {
        val (_, baseOnly) = managers()
        val fields = (0..MAX_FIELD_ENUMERATION_EDGES).map { index ->
            FieldAccessor("Owner", "marked-$index", "Value")
        }
        val storage = baseOnly.methodInitialToFinalApSummariesStorage(inst)
        storage.add(
            fields.mapIndexed { index, field ->
                val memberMark = TaintMarkAccessor("member-$index")
                Edge.FactToFact(
                    entryPoint,
                    baseOnly.exactInitialOf(AccessPathBase.This, field, memberMark),
                    inst,
                    baseOnly.finalOf(AccessPathBase.Return, fields.reversed()[index], memberMark),
                )
            },
            mutableListOf(),
        )

        val stored = mutableListOf<org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder>()
        storage.filterEdgesTo(stored, initialFactPattern = null, finalFactBase = AccessPathBase.Return)
        assertEquals(fields.size, stored.size)
    }

    @Test
    fun `fact side effects and requirements cover Tree filtering and exclusion union`() {
        val (tree, baseOnly) = managers()
        val treeInitialA = tree.initialOf(AccessPathBase.This, exA, fieldA)
        val baseOnlyInitialA = baseOnly.initialOf(AccessPathBase.This, exA, fieldA)
        val treeInitialB = tree.initialOf(AccessPathBase.This, exA, fieldB)
        val baseOnlyInitialB = baseOnly.initialOf(AccessPathBase.This, exA, fieldB)

        val treeSE = tree.factSideEffectSummariesApStorage(inst)
        val baseOnlySE = baseOnly.factSideEffectSummariesApStorage(inst)
        treeSE.add(listOf(FactSideEffectSummary(treeInitialA, kind), FactSideEffectSummary(treeInitialB, kind)), mutableListOf())
        baseOnlySE.add(listOf(FactSideEffectSummary(baseOnlyInitialA, kind), FactSideEffectSummary(baseOnlyInitialB, kind)), mutableListOf())
        treeSE.add(listOf(FactSideEffectSummary(treeInitialA.replaceExclusions(exB), kind)), mutableListOf())
        baseOnlySE.add(listOf(FactSideEffectSummary(baseOnlyInitialA.replaceExclusions(exB), kind)), mutableListOf())

        val treeFiltered = mutableListOf<FactSideEffectSummary>()
        val baseOnlyFiltered = mutableListOf<FactSideEffectSummary>()
        treeSE.filterTaintedTo(treeFiltered, tree.finalOf(AccessPathBase.This, fieldA))
        baseOnlySE.filterTaintedTo(baseOnlyFiltered, baseOnly.finalOf(AccessPathBase.This, fieldA))
        assertEquals(1, treeFiltered.size)
        assertTrue(baseOnlyFiltered.size >= treeFiltered.size)
        assertEquals(exA.union(exB), baseOnlyFiltered.single().initialFactAp.exclusions)

        val treeReq = tree.sideEffectRequirementApStorage()
        val baseOnlyReq = baseOnly.sideEffectRequirementApStorage()
        treeReq.add(listOf(treeInitialA, treeInitialB))
        baseOnlyReq.add(listOf(baseOnlyInitialA, baseOnlyInitialB))
        treeReq.add(listOf(treeInitialA.replaceExclusions(exB)))
        baseOnlyReq.add(listOf(baseOnlyInitialA.replaceExclusions(exB)))
        val treeReqFiltered = mutableListOf<InitialFactAp>()
        val baseOnlyReqFiltered = mutableListOf<InitialFactAp>()
        treeReq.filterTo(treeReqFiltered, tree.finalOf(AccessPathBase.This, fieldA))
        baseOnlyReq.filterTo(baseOnlyReqFiltered, baseOnly.finalOf(AccessPathBase.This, fieldA))
        assertEquals(1, treeReqFiltered.size)
        assertTrue(baseOnlyReqFiltered.size >= treeReqFiltered.size)
        assertEquals(exA.union(exB), baseOnlyReqFiltered.single().exclusions)
        val treeAll = mutableListOf<InitialFactAp>()
        val baseOnlyAll = mutableListOf<InitialFactAp>()
        treeReq.collectAllRequirementsTo(treeAll)
        baseOnlyReq.collectAllRequirementsTo(baseOnlyAll)
        assertEquals(treeAll.size, baseOnlyAll.size)
    }

    @Test
    fun `Z2F F2F and ND subscriptions cover Tree residual modes`() {
        val (tree, baseOnly) = managers()
        val treeSub = tree.accessPathSubscription()
        val baseOnlySub = baseOnly.accessPathSubscription()
        val treeCallerInitial = tree.initialOf(AccessPathBase.Return, ExclusionSet.Empty, fieldB)
        val baseOnlyCallerInitial = baseOnly.initialOf(AccessPathBase.Return, ExclusionSet.Empty, fieldB)
        val treeNdInitial = setOf(treeCallerInitial, tree.initialOf(AccessPathBase.Exception, ExclusionSet.Empty, fieldA))
        val baseOnlyNdInitial = setOf(baseOnlyCallerInitial, baseOnly.initialOf(AccessPathBase.Exception, ExclusionSet.Empty, fieldA))
        val treeExit = tree.finalOf(AccessPathBase.Return, fieldA, mark)
        val baseOnlyExit = baseOnly.finalOf(AccessPathBase.Return, fieldA, mark)
        val treeExactExit = tree.abstractFinalOf(AccessPathBase.Return, fieldA)
        val baseOnlyExactExit = baseOnly.abstractFinalOf(AccessPathBase.Return, fieldA)

        for (exit in listOf(treeExit, treeExactExit)) {
            treeSub.addZeroToFact(inst, AccessPathBase.This, exit)
            treeSub.addFactToFact(inst, AccessPathBase.This, treeCallerInitial, exit)
            treeSub.addNDFactToFact(inst, AccessPathBase.This, treeNdInitial, exit)
        }
        for (exit in listOf(baseOnlyExit, baseOnlyExactExit)) {
            baseOnlySub.addZeroToFact(inst, AccessPathBase.This, exit)
            baseOnlySub.addFactToFact(inst, AccessPathBase.This, baseOnlyCallerInitial, exit)
            baseOnlySub.addNDFactToFact(inst, AccessPathBase.This, baseOnlyNdInitial, exit)
        }
        val treePattern = tree.initialOf(AccessPathBase.This, ExclusionSet.Empty, fieldA)
        val baseOnlyPattern = baseOnly.initialOf(AccessPathBase.This, ExclusionSet.Empty, fieldA)

        val treeZero = mutableListOf<org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.ZeroEdgeSummarySubscription>()
        val baseOnlyZero = mutableListOf<org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.ZeroEdgeSummarySubscription>()
        treeSub.collectZeroEdge(treeZero, treePattern)
        baseOnlySub.collectZeroEdge(baseOnlyZero, baseOnlyPattern)
        assertTrue(baseOnlyZero.size >= treeZero.size, "BaseOnly dropped a Tree Z2F subscription")

        for (empty in listOf(false, true)) {
            val treeFact = mutableListOf<org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.FactEdgeSummarySubscription>()
            val baseOnlyFact = mutableListOf<org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.FactEdgeSummarySubscription>()
            treeSub.collectFactEdge(treeFact, treePattern, empty)
            baseOnlySub.collectFactEdge(baseOnlyFact, baseOnlyPattern, empty)
            assertTrue(
                baseOnlyFact.size >= treeFact.size,
                "BaseOnly candidate broadcast dropped a Tree F2F subscription for empty=$empty",
            )

            val treeNd = mutableListOf<org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.FactNDEdgeSummarySubscription>()
            val baseOnlyNd = mutableListOf<org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.FactNDEdgeSummarySubscription>()
            treeSub.collectFactNDEdge(treeNd, treePattern, empty)
            baseOnlySub.collectFactNDEdge(baseOnlyNd, baseOnlyPattern, empty)
            assertTrue(
                baseOnlyNd.size >= treeNd.size,
                "BaseOnly candidate broadcast dropped a Tree ND subscription for empty=$empty",
            )
        }
    }

    @Test
    fun `final fact list has Tree-equivalent index and LIFO behavior`() {
        val (tree, baseOnly) = managers()
        val treeList = tree.finalFactList()
        val baseOnlyList = baseOnly.finalFactList()
        val treeFacts = listOf(tree.finalOf(AccessPathBase.This, fieldA), tree.finalOf(AccessPathBase.Return, fieldB, mark))
        val baseOnlyFacts = listOf(baseOnly.finalOf(AccessPathBase.This, fieldA), baseOnly.finalOf(AccessPathBase.Return, fieldB, mark))
        treeFacts.forEach(treeList::add)
        baseOnlyFacts.forEach(baseOnlyList::add)
        for (idx in treeFacts.indices) {
            assertFinalCollectionCoversTree(listOf(treeList.get(idx)), listOf(baseOnlyList.get(idx)), "final-list get($idx)")
        }
        assertFinalCollectionCoversTree(listOf(treeList.removeLast()), listOf(baseOnlyList.removeLast()), "final-list removeLast")
    }

    private fun ApManager.finalOf(base: AccessPathBase, vararg accessors: Accessor): FinalFactAp =
        finalOf(base, ExclusionSet.Empty, *accessors)

    private fun ApManager.abstractFinalOf(base: AccessPathBase, vararg accessors: Accessor): FinalFactAp {
        var fact = mostAbstractFinalAp(base)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun ApManager.finalOf(base: AccessPathBase, exclusions: ExclusionSet, vararg accessors: Accessor): FinalFactAp {
        var fact = createFinalAp(base, exclusions)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun ApManager.initialOf(base: AccessPathBase, exclusions: ExclusionSet, vararg accessors: Accessor): InitialFactAp {
        var fact = mostAbstractInitialAp(base).replaceExclusions(exclusions)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun ApManager.exactInitialOf(base: AccessPathBase, vararg accessors: Accessor): InitialFactAp {
        var fact = createFinalInitialAp(base, ExclusionSet.Empty)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun collectFinals(block: (MutableList<FinalFactAp>) -> Unit): List<FinalFactAp> =
        mutableListOf<FinalFactAp>().also(block)

    private fun readable(fact: ReadableAccessorList<*>, sequence: List<Accessor>): Boolean {
        var current: ReadableAccessorList<*> = fact
        for (accessor in sequence) {
            current = current.readAccessor(accessor) as? ReadableAccessorList<*> ?: return false
        }
        return true
    }

    private fun assertFinalCollectionCoversTree(
        tree: Collection<FinalFactAp>,
        baseOnly: Collection<FinalFactAp>,
        scenario: String,
    ) {
        for (base in AccessPathBase.entriesForTest()) {
            for (sequence in listOf(emptyList(), listOf(fieldA), listOf(fieldB), listOf(fieldA, mark), listOf(fieldB, mark))) {
                if (tree.none { it.base == base && readable(it, sequence) }) continue
                assertTrue(
                    baseOnly.any { it.base == base && readable(it, sequence) },
                    "$scenario lost $base ${sequence.joinToString(" -> ")}",
                )
            }
        }
    }

    private fun AccessPathBase.Companion.entriesForTest(): List<AccessPathBase> = listOf(
        AccessPathBase.This,
        AccessPathBase.Return,
        AccessPathBase.Argument(0),
        AccessPathBase.Argument(1),
    )

    private val languageManager = object : LanguageManager {
        override fun getInstIndex(inst: CommonInst): Int = 0
        override fun getMaxInstIndex(method: CommonMethod): Int = 0
        override fun getInstByIndex(method: CommonMethod, index: Int): CommonInst = Companion.inst
        override fun isEmpty(method: CommonMethod): Boolean = false
        override fun getCallExpr(inst: CommonInst): CommonCallExpr? = null
        override fun producesExceptionalControlFlow(inst: CommonInst): Boolean = false
        override fun getCalleeMethod(callExpr: CommonCallExpr): CommonMethod = error("unused")
        override val methodContextSerializer: MethodContextSerializer get() = error("unused")
    }

    private companion object {
        val method = object : CommonMethod {
            override val name: String = "storageDifferential"
            override val parameters: List<CommonMethodParameter> = emptyList()
            override val returnType: CommonTypeName = object : CommonTypeName { override val typeName: String = "void" }
            override fun flowGraph(): ControlFlowGraph<CommonInst> = object : ControlFlowGraph<CommonInst> {
                override val instructions: List<CommonInst> = emptyList()
                override val entries: List<CommonInst> = emptyList()
                override val exits: List<CommonInst> = emptyList()
                override fun successors(node: CommonInst): Set<CommonInst> = emptySet()
                override fun predecessors(node: CommonInst): Set<CommonInst> = emptySet()
            }
        }
        val inst = object : CommonInst {
            override val location: CommonInstLocation = object : CommonInstLocation { override val method: CommonMethod = Companion.method; override val index: Int = 0 }
            override fun toString(): String = "storage-inst"
        }
    }
}
