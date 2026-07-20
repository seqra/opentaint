package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class BaseOnlyInitialAccessIndexTest {
    @Test
    fun `pattern traversal agrees with summary applicability for every packed slot shape`() {
        val accesses = buildList {
            for (staticIdx in intArrayOf(ABSTRACT_MARK, NO_ACCESSOR, 10, 11)) {
                for (fieldIdx in intArrayOf(ABSTRACT_MARK, NO_ACCESSOR, 20, 21)) {
                    for (suffixIdx in intArrayOf(ABSTRACT_MARK, NO_ACCESSOR, 30, 31)) {
                        add(packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx))
                    }
                }
            }
        }
        val index = BaseOnlyInitialAccessIndex<BaseOnlyAccess>()
        accesses.forEach { access -> index.getOrCreate(access) { access } }

        for (pattern in accesses) {
            val actual = hashSetOf<BaseOnlyAccess>()
            index.collectContainedBy(pattern) { access, value ->
                assertEquals(access, value)
                actual += access
            }
            val expected = accesses.filterTo(hashSetOf()) { baseOnlySummaryInitialMatches(pattern, it) }
            assertEquals(expected, actual, "pattern=$pattern")
        }

        val all = hashSetOf<BaseOnlyAccess>()
        index.collectAll { access, _ -> all += access }
        assertEquals(accesses.toSet(), all)
    }

    @Test
    fun `f2f identity and non-identity summaries use the same pattern filter`() {
        val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled)
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(testInst, manager).createStorage()
        val first = packBaseOnlyAccess(NO_ACCESSOR, 20, 30)
        val second = packBaseOnlyAccess(NO_ACCESSOR, 21, 30)
        val identity = packBaseOnlyAccess(NO_ACCESSOR, 22, 30)
        storage.add(
            listOf(
                edge(first, packBaseOnlyAccess(NO_ACCESSOR, 20, 31)),
                edge(second, packBaseOnlyAccess(NO_ACCESSOR, 21, 32)),
                edge(identity, identity),
            ),
            mutableListOf(),
        )

        assertEquals(1, storage.query(first))
        assertEquals(1, storage.query(second))
        assertEquals(1, storage.query(identity), "identity summaries must be filtered too")
        assertEquals(3, storage.query(packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)))
        assertEquals(3, storage.query(null))
    }

    @Test
    fun `identity trie traversal agrees with summary applicability`() {
        val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled)
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(testInst, manager).createStorage()
        val initials = buildList {
            for (staticIdx in intArrayOf(NO_ACCESSOR, 10)) {
                for (fieldIdx in intArrayOf(NO_ACCESSOR, 20, 21)) {
                    for (suffixIdx in intArrayOf(NO_ACCESSOR, 30, 31)) {
                        add(packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx))
                    }
                }
            }
        }
        storage.add(initials.map { edge(it, it) }, mutableListOf())

        val patterns = initials + listOf(
            packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR),
            packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR),
            packBaseOnlyAccess(10, ABSTRACT_MARK, NO_ACCESSOR),
            packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, ABSTRACT_MARK),
            packBaseOnlyAccess(NO_ACCESSOR, 20, ABSTRACT_MARK),
        )
        patterns.forEach { pattern ->
            val expected = initials.count { baseOnlySummaryInitialMatches(pattern, it) }
            assertEquals(expected, storage.query(pattern), "pattern=$pattern")
        }
    }

    @Test
    fun `fact side-effect summaries filter incompatible initials`() {
        val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled)
        val storage = FactSESummariesBaseOnlyStorage(testInst, manager).createStorage()
        val kind = object : SideEffectKind {}
        val first = packBaseOnlyAccess(NO_ACCESSOR, 20, 30)
        val second = packBaseOnlyAccess(NO_ACCESSOR, 21, 30)
        storage.add(first, mapOf(kind to ExclusionSet.Empty), mutableListOf())
        storage.add(second, mapOf(kind to ExclusionSet.Empty), mutableListOf())

        assertEquals(1, storage.query(first))
        assertEquals(1, storage.query(second))
        assertEquals(2, storage.query(packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)))
        assertEquals(2, storage.query(null))
    }

    @Test
    fun `single writer and concurrent readers survive repeated index rehashes`() {
        val index = BaseOnlyInitialAccessIndex<BaseOnlyAccess>()
        val accesses = (0 until 4_000).map { value ->
            packBaseOnlyAccess(100 + value / 1_000, 1_000 + value, 10_000 + value)
        }
        val failures = ConcurrentLinkedQueue<Throwable>()
        val executor = Executors.newFixedThreadPool(5)

        executor.submit {
            try {
                accesses.forEach { access -> index.getOrCreate(access) { access } }
            } catch (t: Throwable) {
                failures += t
            }
        }
        repeat(4) { reader ->
            executor.submit {
                try {
                    repeat(250) {
                        val pattern = if (reader % 2 == 0) {
                            packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR)
                        } else {
                            packBaseOnlyAccess(100 + reader, ABSTRACT_MARK, NO_ACCESSOR)
                        }
                        index.collectContainedBy(pattern) { access, value ->
                            assertEquals(access, value)
                            assertTrue(baseOnlySummaryInitialMatches(pattern, access))
                        }
                    }
                } catch (t: Throwable) {
                    failures += t
                }
            }
        }

        executor.shutdown()
        assertTrue(executor.awaitTermination(30, TimeUnit.SECONDS))
        assertTrue(failures.isEmpty(), failures.joinToString("\n"))

        val eventual = hashSetOf<BaseOnlyAccess>()
        index.collectAll { access, value ->
            assertEquals(access, value)
            eventual += access
        }
        assertEquals(accesses.toSet(), eventual)
    }

    private fun edge(initial: BaseOnlyAccess, final: BaseOnlyAccess) =
        org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary.StorageEdge(
            initial,
            final,
            ExclusionSet.Empty,
        )

    private fun org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary.Storage<BaseOnlyAccess, BaseOnlyAccess>.query(
        pattern: BaseOnlyAccess?,
    ): Int {
        val result = mutableListOf<org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        collectSummariesTo(result, pattern)
        return result.size
    }

    private fun org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.Storage<BaseOnlyAccess, BaseOnlyAccess>.query(
        pattern: BaseOnlyAccess?,
    ): Int {
        val result = mutableListOf<org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.FactSEBuilder<BaseOnlyAccess>>()
        collectSummariesTo(result, pattern)
        return result.size
    }
}

private val testInst = object : org.opentaint.ir.api.common.cfg.CommonInst {
    override val location: org.opentaint.ir.api.common.cfg.CommonInstLocation =
        object : org.opentaint.ir.api.common.cfg.CommonInstLocation {
            override val method: org.opentaint.ir.api.common.CommonMethod
                get() = testMethod
        }
}

private val testMethod = object : org.opentaint.ir.api.common.CommonMethod {
    override val name: String = "baseOnlyInitialAccessIndex"
    override val parameters: List<org.opentaint.ir.api.common.CommonMethodParameter> = emptyList()
    override val returnType: org.opentaint.ir.api.common.CommonTypeName =
        object : org.opentaint.ir.api.common.CommonTypeName {
            override val typeName: String = "java.lang.Object"
        }

    override fun flowGraph(): org.opentaint.ir.api.common.cfg.ControlFlowGraph<org.opentaint.ir.api.common.cfg.CommonInst> =
        object : org.opentaint.ir.api.common.cfg.ControlFlowGraph<org.opentaint.ir.api.common.cfg.CommonInst> {
            override val instructions: List<org.opentaint.ir.api.common.cfg.CommonInst> = emptyList()
            override val entries: List<org.opentaint.ir.api.common.cfg.CommonInst> = emptyList()
            override val exits: List<org.opentaint.ir.api.common.cfg.CommonInst> = emptyList()
            override fun successors(node: org.opentaint.ir.api.common.cfg.CommonInst) = emptySet<org.opentaint.ir.api.common.cfg.CommonInst>()
            override fun predecessors(node: org.opentaint.ir.api.common.cfg.CommonInst) = emptySet<org.opentaint.ir.api.common.cfg.CommonInst>()
        }
}
