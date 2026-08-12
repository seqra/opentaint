package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.util.Cancellation
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class BaseOnlyInitialAccessIndexTest {
    @Test
    fun `pattern traversal agrees with summary applicability for every packed slot shape`() {
        val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, Cancellation())
        val staticA = manager.interner.index(ClassStaticAccessor("S0"))
        val staticB = manager.interner.index(ClassStaticAccessor("S1"))
        val fieldA = manager.interner.index(FieldAccessor("C", "f0", "T"))
        val fieldB = manager.interner.index(FieldAccessor("C", "f1", "T"))
        val markA = manager.interner.index(TaintMarkAccessor("m0"))
        val markB = manager.interner.index(TaintMarkAccessor("m1"))
        val accesses = buildList {
            for (staticIdx in intArrayOf(ABSTRACT_MARK, NO_ACCESSOR, staticA, staticB)) {
                for (fieldIdx in intArrayOf(ABSTRACT_MARK, NO_ACCESSOR, fieldA, fieldB)) {
                    for (suffixIdx in intArrayOf(ABSTRACT_MARK, NO_ACCESSOR, markA, markB)) {
                        val modes = if (suffixIdx == markA || suffixIdx == markB) {
                            BaseOnlyValueAccessorState.entries
                        } else {
                            listOf(BaseOnlyValueAccessorState.Normal)
                        }
                        for (mode in modes) {
                            if (staticIdx == ABSTRACT_MARK &&
                                (fieldIdx != NO_ACCESSOR || suffixIdx != NO_ACCESSOR)
                            ) continue
                            if (fieldIdx == ABSTRACT_MARK && suffixIdx != NO_ACCESSOR) continue
                            if (suffixIdx == NO_ACCESSOR && (staticIdx >= 0 || fieldIdx >= 0)) continue
                            if (staticIdx == NO_ACCESSOR && fieldIdx == NO_ACCESSOR && suffixIdx == NO_ACCESSOR) continue
                            val access = packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx, mode)
                            add(access)
                        }
                    }
                }
            }
        }
        val index = BaseOnlyInitialAccessIndex<BaseOnlyAccess>()
        accesses.forEach { access -> index.getOrCreate(access) { access } }
        accesses.forEach { access -> assertEquals(access, index.get(access)) }

        for (pattern in accesses) {
            val actual = hashSetOf<BaseOnlyAccess>()
            index.collectCandidates(pattern) { access, value ->
                assertEquals(access, value)
                if (baseOnlySummaryInitialMatches(pattern, access)) actual += access
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
        val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, Cancellation())
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(testInst, manager).createStorage()
        val fieldA = manager.interner.index(FieldAccessor("C", "first", "T"))
        val fieldB = manager.interner.index(FieldAccessor("C", "second", "T"))
        val fieldC = manager.interner.index(FieldAccessor("C", "identity", "T"))
        val mark = manager.interner.index(TaintMarkAccessor("initial"))
        val finalA = manager.interner.index(TaintMarkAccessor("final-a"))
        val finalB = manager.interner.index(TaintMarkAccessor("final-b"))
        val first = packBaseOnlyAccess(NO_ACCESSOR, fieldA, mark)
        val second = packBaseOnlyAccess(NO_ACCESSOR, fieldB, mark)
        val identity = packBaseOnlyAccess(NO_ACCESSOR, fieldC, mark)
        storage.add(
            listOf(
                edge(first, packBaseOnlyAccess(NO_ACCESSOR, fieldA, finalA)),
                edge(second, packBaseOnlyAccess(NO_ACCESSOR, fieldB, finalB)),
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
        val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, Cancellation())
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(testInst, manager).createStorage()
        val static = manager.interner.index(ClassStaticAccessor("S"))
        val fieldA = manager.interner.index(FieldAccessor("C", "f0", "T"))
        val fieldB = manager.interner.index(FieldAccessor("C", "f1", "T"))
        val markA = manager.interner.index(TaintMarkAccessor("m0"))
        val markB = manager.interner.index(TaintMarkAccessor("m1"))
        val initials = buildList {
            for (staticIdx in intArrayOf(NO_ACCESSOR, static)) {
                for (fieldIdx in intArrayOf(NO_ACCESSOR, fieldA, fieldB)) {
                    for (suffixIdx in intArrayOf(NO_ACCESSOR, markA, markB)) {
                        val access = packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx)
                        if (!access.isEmpty && suffixIdx != NO_ACCESSOR) add(access)
                    }
                }
            }
        }
        storage.add(initials.map { edge(it, it) }, mutableListOf())

        val patterns = initials + listOf(
            packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR),
            packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR),
            packBaseOnlyAccess(static, ABSTRACT_MARK, NO_ACCESSOR),
            packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, ABSTRACT_MARK),
            packBaseOnlyAccess(NO_ACCESSOR, fieldA, ABSTRACT_MARK),
        )
        patterns.forEach { pattern ->
            val expected = initials.count { baseOnlySummaryInitialMatches(pattern, it) }
            assertEquals(expected, storage.query(pattern), "pattern=$pattern")
        }
    }

    @Test
    fun `fact side-effect summaries filter incompatible initials`() {
        val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, Cancellation())
        val storage = FactSESummariesBaseOnlyStorage(testInst, manager).createStorage()
        val kind = object : SideEffectKind {}
        val fieldA = manager.interner.index(FieldAccessor("C", "f0", "T"))
        val fieldB = manager.interner.index(FieldAccessor("C", "f1", "T"))
        val mark = manager.interner.index(TaintMarkAccessor("effect"))
        val first = packBaseOnlyAccess(NO_ACCESSOR, fieldA, mark)
        val second = packBaseOnlyAccess(NO_ACCESSOR, fieldB, mark)
        storage.add(first, mapOf(kind to ExclusionSet.Empty), mutableListOf())
        storage.add(second, mapOf(kind to ExclusionSet.Empty), mutableListOf())

        assertEquals(1, storage.query(first))
        assertEquals(1, storage.query(second))
        assertEquals(2, storage.query(packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)))
        assertEquals(2, storage.query(null))
    }

    @Test
    fun `single writer and concurrent readers survive repeated index rehashes`() {
        val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, Cancellation())
        val index = BaseOnlyInitialAccessIndex<BaseOnlyAccess>()
        val accesses = (0 until 4_000).map { value ->
            val static = manager.interner.index(ClassStaticAccessor("S${value / 1_000}"))
            val field = manager.interner.index(FieldAccessor("C", "f$value", "T"))
            val mark = manager.interner.index(TaintMarkAccessor("m$value"))
            packBaseOnlyAccess(static, field, mark)
        }
        val readerStatics = IntArray(4) { reader -> manager.interner.index(ClassStaticAccessor("S$reader")) }
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
                            packBaseOnlyAccess(readerStatics[reader], ABSTRACT_MARK, NO_ACCESSOR)
                        }
                        index.collectCandidates(pattern) { access, value ->
                            assertEquals(access, value)
                            // Routing may conservatively return false-positive candidates.
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
