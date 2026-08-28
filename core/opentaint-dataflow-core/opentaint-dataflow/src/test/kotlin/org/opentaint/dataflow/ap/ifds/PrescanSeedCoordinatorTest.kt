package org.opentaint.dataflow.ap.ifds

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy.AnyAccessorDisabled
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.serialization.MethodContextSerializer
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class PrescanSeedCoordinatorTest {
    private val apManager = TreeApManager(AnyAccessorDisabled, RefManager(), Cancellation())

    @Test
    fun `global seed reaches active targets once`() {
        val producer = method("producer")
        val consumer = method("consumer")
        val producerEntry = entryPoint(producer)
        val consumerEntry = entryPoint(consumer)
        val fact = fact(AccessPathBase.ClassStatic, "global")
        val coordinator = coordinator(producer, consumer)

        assertTrue(coordinator.activate(consumerEntry).isEmpty())

        val first = coordinator.acceptSummaryEdges(producerEntry, listOf(z2f(producerEntry, fact)))
        assertEquals(listOf(consumerEntry), first.map { it.methodEntryPoint })
        assertEquals(listOf(fact), first.single().facts)

        assertTrue(coordinator.acceptSummaryEdges(producerEntry, listOf(z2f(producerEntry, fact))).isEmpty())
        assertEquals(1, coordinator.stats().globalSeeds)
        assertEquals(1, coordinator.stats().duplicates)
    }

    @Test
    fun `global seed is replayed when consumer activates later`() {
        val producer = method("producer")
        val consumer = method("consumer")
        val producerEntry = entryPoint(producer)
        val consumerEntry = entryPoint(consumer)
        val fact = fact(AccessPathBase.ClassStatic, "global")
        val coordinator = coordinator(producer, consumer)

        assertTrue(coordinator.acceptSummaryEdges(producerEntry, listOf(z2f(producerEntry, fact))).isEmpty())

        val replay = coordinator.activate(consumerEntry)
        assertEquals(listOf(fact), replay.single().facts)
        assertTrue(coordinator.activate(consumerEntry).isEmpty())
        assertEquals(1, coordinator.stats().replayedEntryPoints)
    }

    @Test
    fun `constructor receiver seed reaches only receiver targets of same owner`() {
        val constructor = method("init", initializerOwner = "A", receiverOwner = "A")
        val sameOwner = method("same", receiverOwner = "A")
        val staticSameOwner = method("static")
        val otherOwner = method("other", receiverOwner = "B")
        val constructorEntry = entryPoint(constructor)
        val sameEntry = entryPoint(sameOwner)
        val staticEntry = entryPoint(staticSameOwner)
        val otherEntry = entryPoint(otherOwner)
        val fact = fact(AccessPathBase.This, "receiver")
        val coordinator = coordinator(constructor, sameOwner, staticSameOwner, otherOwner)

        coordinator.activate(sameEntry)
        coordinator.activate(staticEntry)
        coordinator.activate(otherEntry)

        val deliveries = coordinator.acceptSummaryEdges(constructorEntry, listOf(z2f(constructorEntry, fact)))

        assertEquals(listOf(sameEntry), deliveries.map { it.methodEntryPoint })
        assertEquals(listOf(fact), deliveries.single().facts)
        assertEquals(1, coordinator.stats().constructorSeeds)
    }

    @Test
    fun `this fact from ordinary method is not owner propagated`() {
        val producer = method("ordinary", receiverOwner = "A")
        val consumer = method("consumer", receiverOwner = "A")
        val producerEntry = entryPoint(producer)
        val coordinator = coordinator(producer, consumer)

        coordinator.activate(entryPoint(consumer))

        val deliveries = coordinator.acceptSummaryEdges(
            producerEntry,
            listOf(z2f(producerEntry, fact(AccessPathBase.This, "receiver"))),
        )
        assertTrue(deliveries.isEmpty())
        assertEquals(0, coordinator.stats().constructorSeeds)
    }

    @Test
    fun `constructor receiver seed from outside project scope is not propagated`() {
        val dependencyConstructor = method("init", initializerOwner = "A", receiverOwner = "A")
        val consumer = method("consumer", receiverOwner = "A")
        val dependencyEntry = entryPoint(dependencyConstructor)
        val coordinator = coordinator(consumer)

        coordinator.activate(entryPoint(consumer))

        val deliveries = coordinator.acceptSummaryEdges(
            dependencyEntry,
            listOf(z2f(dependencyEntry, fact(AccessPathBase.This, "receiver"))),
        )
        assertTrue(deliveries.isEmpty())
        assertEquals(0, coordinator.stats().constructorSeeds)
    }

    @Test
    fun `constructor receiver seed is replayed to a later same-owner activation`() {
        val constructor = method("init", initializerOwner = "A", receiverOwner = "A")
        val consumer = method("consumer", receiverOwner = "A")
        val constructorEntry = entryPoint(constructor)
        val consumerEntry = entryPoint(consumer)
        val fact = fact(AccessPathBase.This, "receiver")
        val coordinator = coordinator(constructor, consumer)

        assertTrue(coordinator.acceptSummaryEdges(constructorEntry, listOf(z2f(constructorEntry, fact))).isEmpty())

        val replay = coordinator.activate(consumerEntry)
        assertEquals(listOf(fact), replay.single().facts)
        assertEquals(1, coordinator.stats().constructorDeliveries)
    }

    @Test
    fun `non-static facts and non-Z2F edges do not propagate`() {
        val producer = method("producer")
        val consumer = method("consumer")
        val producerEntry = entryPoint(producer)
        val coordinator = coordinator(producer, consumer)
        coordinator.activate(entryPoint(consumer))

        val ignored = listOf(
            z2f(producerEntry, fact(AccessPathBase.Return, "return")),
            Edge.ZeroToZero(producerEntry, producerEntry.statement),
        )

        assertTrue(coordinator.acceptSummaryEdges(producerEntry, ignored).isEmpty())
        assertEquals(0, coordinator.stats().globalSeeds)
        assertEquals(0, coordinator.stats().constructorSeeds)
    }

    @Test
    fun `default summary subscriber observes canonical deltas after reset`() {
        val producer = method("producer")
        val producerEntry = entryPoint(producer)
        val edge = z2f(producerEntry, fact(AccessPathBase.ClassStatic, "global"))
        val received = mutableListOf<List<Edge>>()
        val subscriber = object : SummaryEdgeStorageWithSubscribers.Subscriber {
            override fun newSummaryEdges(edges: List<Edge>) {
                received += edges
            }

            override fun newSideEffectRequirement(
                methodEntryPoint: MethodEntryPoint,
                requirements: List<InitialFactAp>,
            ) = Unit

            override fun newSideEffectSummaries(
                methodEntryPoint: MethodEntryPoint,
                sideEffects: List<SideEffectSummary>,
            ) = Unit
        }
        val storage = MethodSummariesUnitStorage(apManager, DummyLanguageManager, subscriber)

        storage.addSummaryEdges(producerEntry, listOf(edge))
        storage.addSummaryEdges(producerEntry, listOf(edge))
        assertEquals(1, received.size)
        assertEquals(listOf<Edge>(edge), received.single())

        storage.resetApManager(apManager)
        storage.addSummaryEdges(producerEntry, listOf(edge))
        assertEquals(2, received.size)
        assertTrue(received.all { it == listOf<Edge>(edge) })
    }

    private fun coordinator(vararg methods: DummyMethod) = PrescanSeedCoordinator(methods.toList(), Policy)

    private fun fact(base: AccessPathBase, mark: String): FinalFactAp =
        apManager.createFinalAp(base, ExclusionSet.Universe).prependAccessor(TaintMarkAccessor(mark))

    private fun z2f(entryPoint: MethodEntryPoint, fact: FinalFactAp) =
        Edge.ZeroToFact(entryPoint, entryPoint.statement, fact)

    private fun method(
        name: String,
        initializerOwner: String? = null,
        receiverOwner: String? = null,
    ) = DummyMethod(name, initializerOwner, receiverOwner)

    private fun entryPoint(method: DummyMethod): MethodEntryPoint =
        MethodEntryPoint(EmptyMethodContext, DummyInst(DummyLocation(method, 0)))

    private data class DummyMethod(
        override val name: String,
        val initializerOwner: String?,
        val receiverOwner: String?,
    ) : CommonMethod {
        override val parameters: List<CommonMethodParameter> = emptyList()
        override val returnType: CommonTypeName get() = error("Unsupported")
        override fun flowGraph(): ControlFlowGraph<CommonInst> = error("Unsupported")
    }

    private data class DummyLocation(
        override val method: CommonMethod,
        override val index: Int,
    ) : CommonInstLocation

    private data class DummyInst(
        override val location: CommonInstLocation,
    ) : CommonInst

    private data object Policy : PrescanPropagationPolicy {
        override fun initializerOwner(method: CommonMethod): PrescanInitializerOwner? =
            (method as DummyMethod).initializerOwner?.let(::PrescanInitializerOwner)

        override fun receiverOwner(method: CommonMethod): PrescanInitializerOwner? =
            (method as DummyMethod).receiverOwner?.let(::PrescanInitializerOwner)
    }

    private data object DummyLanguageManager : LanguageManager {
        override fun getInstIndex(inst: CommonInst): Int = error("Unsupported")
        override fun getMaxInstIndex(method: CommonMethod): Int = error("Unsupported")
        override fun getInstByIndex(method: CommonMethod, index: Int): CommonInst = error("Unsupported")
        override fun isEmpty(method: CommonMethod): Boolean = error("Unsupported")
        override fun getCallExpr(inst: CommonInst): CommonCallExpr? = error("Unsupported")
        override fun producesExceptionalControlFlow(inst: CommonInst): Boolean = error("Unsupported")
        override fun getCalleeMethod(callExpr: CommonCallExpr): CommonMethod = error("Unsupported")
        override val methodContextSerializer: MethodContextSerializer get() = error("Unsupported")
    }
}
