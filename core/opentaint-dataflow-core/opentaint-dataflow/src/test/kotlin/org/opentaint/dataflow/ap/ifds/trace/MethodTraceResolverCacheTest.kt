package org.opentaint.dataflow.ap.ifds.trace

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import java.util.concurrent.CountDownLatch
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicInteger
import kotlin.test.assertEquals

class MethodTraceResolverCacheTest {
    @Test
    fun `concurrent resolvers compute a shared value once`() {
        val cache = MethodTraceResolver.Cache()
        val computations = AtomicInteger()
        val start = CountDownLatch(1)
        val executor = Executors.newFixedThreadPool(8)

        try {
            val tasks = List(32) {
                executor.submit<List<MethodEntryPoint>> {
                    start.await()
                    cache.calleeEntryPoints(statement) {
                        computations.incrementAndGet()
                        emptyList()
                    }
                }
            }
            start.countDown()
            tasks.forEach { assertEquals(emptyList(), it.get(5, TimeUnit.SECONDS)) }
        } finally {
            executor.shutdownNow()
        }

        assertEquals(1, computations.get())
    }

    private val statement = object : CommonInst {
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val index: Int = 0
            override val method: CommonMethod = object : CommonMethod {
                override val name: String = "cache-test"
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
        }
    }
}
