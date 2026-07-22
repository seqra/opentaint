package org.opentaint.dataflow.ap.ifds.access.suffix

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.FactEdgeSummarySubscription
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

class MethodEdgesInitialToFinalSuffixTreeSetTest {
    private val manager = SuffixTreeApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled)
    private val statement = IndexedInst(0)
    private val languageManager = object : LanguageManager {
        override fun getInstIndex(inst: CommonInst): Int = (inst as IndexedInst).index
        override fun getMaxInstIndex(method: CommonMethod): Int = 0
        override fun getInstByIndex(method: CommonMethod, index: Int): CommonInst = statement
        override fun isEmpty(method: CommonMethod): Boolean = false
        override fun getCallExpr(inst: CommonInst) = error("unused")
        override fun producesExceptionalControlFlow(inst: CommonInst): Boolean = false
        override fun getCalleeMethod(callExpr: org.opentaint.ir.api.common.cfg.CommonCallExpr): CommonMethod =
            error("unused")
        override val methodContextSerializer: org.opentaint.dataflow.ap.ifds.serialization.MethodContextSerializer
            get() = error("unused")
    }

    @Test
    fun `store emits one branching identity bundle`() = with(manager) {
        val first = FieldAccessor("T", "first", "T").idx
        val second = FieldAccessor("T", "second", "T").idx
        val store = MethodEdgesInitialToFinalSuffixTreeSet(
            statement,
            maxInstIdx = 0,
            languageManager,
            manager,
        )

        val base = AccessPathBase.Argument(0)
        store.addFactToFact(statement, initial(first), final(first, base), suffixBundle = null)
        val additions = store.addFactToFact(statement, initial(second), final(second, base), suffixBundle = null)

        val addition = additions.single()
        val publishedBundle = assertNotNull(addition.suffixBundle)
        assertEquals(
            setOf(listOf(first), listOf(second)),
            publishedBundle.suffixTree.cones().map { it.suffix }.toSet(),
        )
        assertTrue(publishedBundle.suffixTree.isBranching())
        val storedBundle = store.bundlesAt(statement).single()
        assertEquals(
            setOf(listOf(first), listOf(second)),
            storedBundle.suffixTree.cones().mapTo(hashSetOf()) { it.suffix },
        )
        assertTrue(storedBundle.suffixTree.isBranching())
    }

    @Test
    fun `summary emits one branching identity bundle`() = with(manager) {
        val first = FieldAccessor("T", "first", "T").idx
        val second = FieldAccessor("T", "second", "T").idx
        val summaries = MethodInitialToFinalSuffixTreeSummaries(statement, manager)
        val entryPoint = MethodEntryPoint(EmptyMethodContext, statement)

        summaries.add(
            listOf(
                Edge.FactToFact(
                    entryPoint,
                    initial(first),
                    statement,
                    final(first, AccessPathBase.Argument(0)),
                )
            ),
            mutableListOf(),
        )
        val additions = mutableListOf<FactToFactEdgeBuilder>()
        summaries.add(
            listOf(
                Edge.FactToFact(
                    entryPoint,
                    initial(second),
                    statement,
                    final(second, AccessPathBase.Argument(0)),
                )
            ),
            additions,
        )

        val storedBundle = summaries.allBundles().single()
        assertEquals(1, additions.size)
        assertEquals(
            setOf(listOf(first), listOf(second)),
            storedBundle.suffixTree.cones().mapTo(hashSetOf()) { it.suffix },
        )
        assertTrue(storedBundle.suffixTree.isBranching())
        val publishedBundle = assertNotNull(additions.single().setEntryPoint(entryPoint).build().suffixBundle)
        assertEquals(
            setOf(listOf(first), listOf(second)),
            publishedBundle.suffixTree.cones().map { it.suffix }.toSet(),
        )
        assertTrue(publishedBundle.suffixTree.isBranching())
        Unit
    }

    @Test
    fun `subscription emits one branching identity bundle`() = with(manager) {
        val first = FieldAccessor("T", "first", "T").idx
        val second = FieldAccessor("T", "second", "T").idx
        val subscriptions = MethodSuffixTreeAccessPathSubscription(manager)
        val base = AccessPathBase.Argument(0)

        subscriptions.addFactToFactEdges(
            statement,
            base,
            initial(first),
            final(first, base),
            suffixBundle = null,
        )
        val additions = subscriptions.addFactToFactEdges(
            statement,
            base,
            initial(second),
            final(second, base),
            suffixBundle = null,
        )

        val storedBundle = subscriptions.allBundles().single()
        assertEquals(1, additions.size)
        assertEquals(
            setOf(listOf(first), listOf(second)),
            storedBundle.suffixTree.cones().mapTo(hashSetOf()) { it.suffix },
        )
        assertTrue(storedBundle.suffixTree.isBranching())
        val publishedBundle = assertNotNull(
            additions.single()
                .setStatements(MethodEntryPoint(EmptyMethodContext, statement), statement)
                .callerPathEdge
                .suffixBundle
        )
        assertEquals(
            setOf(listOf(first), listOf(second)),
            publishedBundle.suffixTree.cones().map { it.suffix }.toSet(),
        )
        assertTrue(publishedBundle.suffixTree.isBranching())
        Unit
    }

    @Test
    fun `covered subscription keeps concrete witness for later summary lookup`() = with(manager) {
        val field = FieldAccessor("T", "field", "T").idx
        val subscriptions = MethodSuffixTreeAccessPathSubscription(manager)
        val base = AccessPathBase.Argument(0)
        val rootInitial = AccessPath(manager, base, access = null, ExclusionSet.Empty)
        val rootFinal = AccessTree(manager, base, manager.abstractNode, ExclusionSet.Empty)

        subscriptions.addFactToFactEdges(
            statement,
            base,
            rootInitial,
            rootFinal,
            suffixBundle = null,
        )
        subscriptions.addFactToFactEdges(
            statement,
            base,
            initial(field),
            final(field, base),
            suffixBundle = null,
        )

        // The propagated relation canonically annihilates the covered child cone.
        assertEquals(listOf(emptyList()), subscriptions.allBundles().single().suffixTree.cones().map { it.suffix })

        val matches = mutableListOf<FactEdgeSummarySubscription>()
        subscriptions.collectFactEdge(matches, initial(field), emptyDeltaRequired = false)

        val matched = matches.single()
            .setStatements(MethodEntryPoint(EmptyMethodContext, statement), statement)
            .callerPathEdge
        val matchedAccess = (matched.initialFactAp as AccessPath).access!!.toList()
        assertEquals(listOf(field), List(matchedAccess.size) { matchedAccess.getInt(it) })
    }

    @Test
    fun `many diagonal edges remain one stored bundle`() {
        val treeManager = TreeApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled)
        val suffixManager = SuffixTreeApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled)
        val treeStore = treeManager.methodEdgesInitialToFinalApSet(statement, 0, languageManager)
        val suffixStore = suffixManager.methodEdgesInitialToFinalApSet(statement, 0, languageManager)
            as MethodEdgesInitialToFinalSuffixTreeSet
        val initialPrefix = FieldAccessor("T", "initialPrefix", "T")
        val finalPrefix = FieldAccessor("T", "finalPrefix", "T")
        val alphabet = (0 until 12).map { FieldAccessor("T", "suffix$it", "T") }
        val suffixes = buildList {
            for (first in alphabet) {
                for (second in alphabet) {
                    if (first != second) add(listOf(first, second))
                }
            }
        }

        for (suffix in suffixes) {
            treeStore.add(
                statement,
                initialFact(treeManager, listOf(initialPrefix) + suffix),
                finalFact(treeManager, listOf(finalPrefix) + suffix),
            )
            suffixStore.add(
                statement,
                initialFact(suffixManager, listOf(initialPrefix) + suffix),
                finalFact(suffixManager, listOf(finalPrefix) + suffix),
            )
        }

        val treeEdges = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        treeStore.collectApAtStatement(treeEdges, statement)
        val bundle = suffixStore.bundlesAt(statement).single()
        assertEquals(suffixes.size, treeEdges.size)
        assertEquals(suffixes.size, bundle.suffixTree.cones().size)
        assertTrue(bundle.suffixTree.isBranching())
    }

    @Test
    fun `materialization restores field uniqueness at both seams`() = with(manager) {
        val repeated = FieldAccessor("T", "repeated", "T").idx
        val tail = FieldAccessor("T", "tail", "T").idx
        val suffixTree = SuffixRelationTrie().also {
            it.add(
                SuffixGenerator(
                    initialPrefix = listOf(repeated),
                    finalPrefix = listOf(repeated),
                    suffix = listOf(repeated, tail),
                    exclusions = emptySet(),
                )
            )
        }.bundles().single().suffixTree
        val bundle = SuffixEdgeBundle(
            initialPrefix = listOf(repeated),
            finalPrefixTree = FinalPrefixTree.single(
                listOf(repeated),
                FinalPrefixMarkers(isFinal = false, isAbstract = true),
            ),
            suffixTree = suffixTree,
        )
        val edge = Edge.FactToFact(
            MethodEntryPoint(EmptyMethodContext, statement),
            initialPrefix(repeated),
            statement,
            finalPrefix(repeated),
            bundle,
        )

        val materialized = edge.materializeSuffixes().single()
        val initialAccessors = (materialized.initialFactAp as AccessPath).access!!.toList()
        assertEquals(listOf(repeated, tail), List(initialAccessors.size) { initialAccessors.getInt(it) })

        val finalAccessors = ArrayList<Int>()
        var finalNode = (materialized.factAp as AccessTree).access
        while (true) {
            var next: Pair<Int, AccessTree.AccessNode>? = null
            finalNode.forEachAccessor { accessor, child -> next = accessor to child }
            val current = next ?: break
            finalAccessors.add(current.first)
            finalNode = current.second
        }
        assertEquals(listOf(repeated, tail), finalAccessors)
    }

    private fun initial(accessor: Int) = AccessPath(
        manager,
        AccessPathBase.Argument(0),
        manager.buildInitialPath(listOf(accessor)),
        ExclusionSet.Empty,
    )

    private fun final(accessor: Int, base: AccessPathBase = AccessPathBase.Return) = AccessTree(
        manager,
        base,
        manager.buildFinalPath(listOf(accessor), FinalPrefixMarkers(false, true))!!,
        ExclusionSet.Empty,
    )

    private fun initialPrefix(accessor: Int) = initial(accessor)
    private fun finalPrefix(accessor: Int) = AccessTree(
        manager,
        AccessPathBase.Return,
        manager.buildFinalPath(listOf(accessor), FinalPrefixMarkers(false, true))!!,
        ExclusionSet.Empty,
    )

    private fun initialFact(manager: TreeApManager, accessors: List<FieldAccessor>): InitialFactAp {
        var fact = manager.mostAbstractInitialAp(AccessPathBase.This)
        accessors.asReversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun finalFact(manager: TreeApManager, accessors: List<FieldAccessor>): FinalFactAp {
        var fact = manager.createAbstractAp(AccessPathBase.Return, ExclusionSet.Empty)
        accessors.asReversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private class IndexedInst(val index: Int) : CommonInst {
            override val location: CommonInstLocation = object : CommonInstLocation {
            override val method: CommonMethod = object : CommonMethod {
                override val name: String = "suffixTest"
                override val parameters: List<CommonMethodParameter> = listOf(
                    object : CommonMethodParameter {
                        override val type: CommonTypeName = object : CommonTypeName {
                            override val typeName: String = "T"
                        }
                    }
                )
                override val returnType: CommonTypeName = object : CommonTypeName {
                    override val typeName: String = "void"
                }
                override fun flowGraph(): ControlFlowGraph<CommonInst> = object : ControlFlowGraph<CommonInst> {
                    override val instructions: List<CommonInst> = listOf(this@IndexedInst)
                    override val entries: List<CommonInst> = instructions
                    override val exits: List<CommonInst> = instructions
                    override fun successors(node: CommonInst): Set<CommonInst> = emptySet()
                    override fun predecessors(node: CommonInst): Set<CommonInst> = emptySet()
                }
            }
        }
    }
}
