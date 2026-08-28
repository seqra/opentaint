package org.opentaint.dataflow.ap.ifds

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy.AnyAccessorDisabled
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.serialization.MethodContextSerializer
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.ifds.UnitType
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
    fun `global seed reaches all scope targets once`() {
        val producer = method("producer")
        val consumer = method("consumer")
        val producerEntry = entryPoint(producer)
        val consumerEntry = entryPoint(consumer)
        val fact = fact(AccessPathBase.ClassStatic, "global")
        val coordinator = coordinator(producer, consumer)

        val first = coordinator.acceptSummaryEdges(producerEntry, listOf(z2f(producerEntry, fact)))
        assertTrue(first.all { it.sourceMethod == producer })
        assertEquals(setOf(producerEntry, consumerEntry), first.mapTo(hashSetOf()) { it.methodEntryPoint })
        assertTrue(first.all { it.facts == listOf(fact) })

        assertTrue(coordinator.acceptSummaryEdges(producerEntry, listOf(z2f(producerEntry, fact))).isEmpty())
        assertEquals(1, coordinator.stats().globalSeeds)
        assertEquals(1, coordinator.stats().duplicates)
    }

    @Test
    fun `global seed always targets empty context`() {
        val producer = method("producer")
        val consumer = method("consumer")
        val producerEntry = MethodEntryPoint(DummyContext, producer.entry)
        val fact = fact(AccessPathBase.ClassStatic, "global")
        val coordinator = coordinator(producer, consumer)

        val deliveries = coordinator.acceptSummaryEdges(producerEntry, listOf(z2f(producerEntry, fact)))
        assertTrue(deliveries.all { it.methodEntryPoint.context == EmptyMethodContext })
        assertEquals(
            setOf<CommonMethod>(producer, consumer),
            deliveries.mapTo(hashSetOf()) { it.methodEntryPoint.method },
        )
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

        val deliveries = coordinator.acceptSummaryEdges(constructorEntry, listOf(z2f(constructorEntry, fact)))

        assertEquals(setOf(constructorEntry, sameEntry), deliveries.mapTo(hashSetOf()) { it.methodEntryPoint })
        assertTrue(deliveries.all { it.facts == listOf(fact) })
        assertTrue(staticEntry !in deliveries.map { it.methodEntryPoint })
        assertTrue(otherEntry !in deliveries.map { it.methodEntryPoint })
        assertEquals(1, coordinator.stats().constructorSeeds)
    }

    @Test
    fun `this fact from ordinary method is not owner propagated`() {
        val producer = method("ordinary", receiverOwner = "A")
        val consumer = method("consumer", receiverOwner = "A")
        val producerEntry = entryPoint(producer)
        val coordinator = coordinator(producer, consumer)

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

        val deliveries = coordinator.acceptSummaryEdges(
            dependencyEntry,
            listOf(z2f(dependencyEntry, fact(AccessPathBase.This, "receiver"))),
        )
        assertTrue(deliveries.isEmpty())
        assertEquals(0, coordinator.stats().constructorSeeds)
    }

    @Test
    fun `constructor receiver seed reaches every same-owner scope method`() {
        val constructor = method("init", initializerOwner = "A", receiverOwner = "A")
        val consumer = method("consumer", receiverOwner = "A")
        val constructorEntry = entryPoint(constructor)
        val consumerEntry = entryPoint(consumer)
        val fact = fact(AccessPathBase.This, "receiver")
        val coordinator = coordinator(constructor, consumer)

        val deliveries = coordinator.acceptSummaryEdges(constructorEntry, listOf(z2f(constructorEntry, fact)))
        assertTrue(deliveries.all { it.sourceMethod == constructor })
        assertEquals(setOf(constructorEntry, consumerEntry), deliveries.mapTo(hashSetOf()) { it.methodEntryPoint })
        assertTrue(deliveries.all { it.facts == listOf(fact) })
        assertEquals(2, coordinator.stats().constructorDeliveries)
    }

    @Test
    fun `non-static facts and non-Z2F edges do not propagate`() {
        val producer = method("producer")
        val consumer = method("consumer")
        val producerEntry = entryPoint(producer)
        val coordinator = coordinator(producer, consumer)

        val ignored = listOf(
            z2f(producerEntry, fact(AccessPathBase.Return, "return")),
            Edge.ZeroToZero(producerEntry, producerEntry.statement),
        )

        assertTrue(coordinator.acceptSummaryEdges(producerEntry, ignored).isEmpty())
        assertEquals(0, coordinator.stats().globalSeeds)
        assertEquals(0, coordinator.stats().constructorSeeds)
    }

    @Test
    fun `new summary storage hook routes facts from the producer unit`() {
        val producer = method("producer")
        val consumer = method("consumer")
        val producerEntry = entryPoint(producer)
        val fact = fact(AccessPathBase.ClassStatic, "global")
        val manager = RecordingRunnerManager()
        val propagation = PrescanPropagation()

        propagation.start(listOf(producer, consumer), manager)
        val storage = SummaryEdgeStorageWithSubscribers(apManager, producerEntry)
        propagation.onNewSummaryStorage(storage, manager)
        storage.addEdges(listOf(z2f(producerEntry, fact)))
        assertEquals(
            setOf<CommonMethod>(producer, consumer),
            manager.routedFacts.mapTo(hashSetOf()) { it.methodEntryPoint.method },
        )
        assertTrue(manager.routedFacts.all { it.callerUnit == DummyUnit(producer.name) })
        assertTrue(manager.routedFacts.all { it.methodEntryPoint.context == EmptyMethodContext })
        assertTrue(manager.routedFacts.all { it.fact == fact })

        propagation.finish()
        val inactiveStorage = SummaryEdgeStorageWithSubscribers(apManager, producerEntry)
        propagation.onNewSummaryStorage(inactiveStorage, manager)
        inactiveStorage.addEdges(listOf(z2f(producerEntry, fact(AccessPathBase.ClassStatic, "later"))))
        assertEquals(2, manager.routedFacts.size)
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
        val storage = MethodSummariesUnitStorage(apManager, DummyLanguageManager) {
            it.subscribeOnEdges(subscriber)
        }

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
        MethodEntryPoint(EmptyMethodContext, method.entry)

    private data object DummyContext : MethodContext

    private data class DummyMethod(
        override val name: String,
        val initializerOwner: String?,
        val receiverOwner: String?,
    ) : CommonMethod {
        override val parameters: List<CommonMethodParameter> = emptyList()
        override val returnType: CommonTypeName get() = error("Unsupported")
        val entry: CommonInst = DummyInst(DummyLocation(this, 0))
        override fun flowGraph(): ControlFlowGraph<CommonInst> = object : ControlFlowGraph<CommonInst> {
            override val instructions: List<CommonInst> = listOf(entry)
            override val entries: List<CommonInst> = listOf(entry)
            override val exits: List<CommonInst> = listOf(entry)
            override fun successors(node: CommonInst): Set<CommonInst> = emptySet()
            override fun predecessors(node: CommonInst): Set<CommonInst> = emptySet()
        }
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

    private data class DummyUnit(val name: String) : UnitType

    private data class RoutedFact(
        val callerUnit: UnitType,
        val methodEntryPoint: MethodEntryPoint,
        val fact: FinalFactAp,
    )

    private class RecordingRunnerManager : AnalysisUnitRunnerManager {
        override val unitResolver = UnitResolver<CommonMethod> { DummyUnit(it.name) }
        override val cancellation = Cancellation()
        val routedFacts = mutableListOf<RoutedFact>()

        override fun getOrCreateUnitStorage(unit: UnitType): MethodSummariesUnitStorage? = null
        override fun getOrCreateUnitRunner(unit: UnitType): AnalysisRunner? = null
        override fun registerMethodCallFromUnit(method: CommonMethod, unit: UnitType) = Unit

        override fun handleCrossUnitFactCall(
            callerUnit: UnitType,
            methodEntryPoint: MethodEntryPoint,
            methodFactAp: FinalFactAp,
        ) {
            routedFacts += RoutedFact(callerUnit, methodEntryPoint, methodFactAp)
        }
    }
}
