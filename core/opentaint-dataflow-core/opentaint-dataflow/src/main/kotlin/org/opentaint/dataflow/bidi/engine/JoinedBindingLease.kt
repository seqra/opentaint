package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId
import java.util.IdentityHashMap

internal enum class JoinedPreparationPhase { CAPTURED, SEALED, RELEASED, BEFORE_BIND, BOUND, CLOSED }

/** Plain stopped-owner values. No actor, runtime, runner or callback is captured. */
internal class JoinedStaticSource(
    val owner: OwnedScope,
    private val root: RunSummaryStore?,
    private val ports: PortSummaryStores?,
    val outgoingDemandTargets: Set<TargetSummary>,
    val privateSeeds: StaticGuidanceSeedStore,
    private val rawWrites: KilledStaticWriteStore,
) {
    fun exitStores(): Sequence<Pair<PortId, RunSummaryStore>> =
        root?.let { sequenceOf(PortId.ROOT_EXIT to it) } ?: checkNotNull(ports).entries()
    fun freezeWrites(): FrozenStaticWrites = rawWrites.freeze(
        exitStores().flatMap { it.second.all() }, privateSeeds.frozenRows())
}

/** Joined-only directories. Every map entry keeps its original complete owner key. */
internal class JoinedBindingLease : AutoCloseable {
    private val local = LinkedHashMap<OwnedScope, JoinedLocalInputs>()
    private val callerOwners = IdentityHashMap<SubscriptionManager, JoinedCallerInputs>()
    private val callers = LinkedHashMap<MethodKey, List<JoinedCallerInputs>>()
    private var closed = false

    fun addLocal(method: MethodKey, inputs: Map<BlockScope, JoinedLocalInputs>) {
        check(!closed)
        try {
            for ((scope, reader) in inputs) {
                val owner = OwnedScope(method, scope)
                check(owner !in local) { "Joined local owner was already captured" }
                local[owner] = reader
            }
        } catch (error: Throwable) {
            // The lease retains registered owners; close every reader it failed to adopt.
            for ((scope, reader) in inputs) if (local[OwnedScope(method, scope)] !== reader) try {
                reader.close()
            } catch (closeError: Throwable) { if (closeError !== error) error.addSuppressed(closeError) }
            throw error
        }
    }
    fun addCallers(storage: SummaryStorage) {
        check(!closed)
        callers[storage.method] = storage.detachJoinedSubscribers { subscriber ->
            callerOwners[subscriber] ?: subscriber.detachJoinedInputs().also { reader ->
                try { callerOwners[subscriber] = reader } catch (error: Throwable) {
                    try { reader.close() } catch (closeError: Throwable) {
                        if (closeError !== error) error.addSuppressed(closeError)
                    }
                    throw error
                }
            }
        }
    }
    fun visitLocalInputs(owner: OwnedScope, visit: (LocalLink, Facts) -> Unit) {
        check(!closed) { "Joined binding lease is closed" }
        local[owner]?.visit(visit)
    }
    fun visitCallerInputs(method: MethodKey, writer: Publication, mode: ApMode, visit: (Subscription) -> Unit) {
        check(!closed) { "Joined binding lease is closed" }
        for (reader in callers[method].orEmpty()) reader.visit(method, writer, mode, visit)
    }
    override fun close() {
        if (closed) return
        closed = true
        var failure: Throwable? = null
        fun close(action: () -> Unit) {
            try { action() } catch (error: Throwable) {
                val first = failure
                if (first == null) failure = error else if (first !== error) first.addSuppressed(error)
            }
        }
        for (reader in local.values) close { reader.close() }
        for (reader in callerOwners.values) close { reader.close() }
        local.clear(); callers.clear(); callerOwners.clear()
        failure?.let { throw it }
    }
}
