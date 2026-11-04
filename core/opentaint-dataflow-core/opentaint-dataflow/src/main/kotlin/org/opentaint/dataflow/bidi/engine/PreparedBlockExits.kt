package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.*
import java.util.BitSet
import java.util.Collections

/** Routing annotation only. It never enters AP, publication, native-record or report equality. */
internal sealed interface PreparedExit {
    data object DeadData : PreparedExit
    class Routes(routes: List<MethodBlockRoute>) : PreparedExit {
        val routes: List<MethodBlockRoute> = Collections.unmodifiableList(routes.toList())
    }
    class ActualStarts internal constructor(private val allowed: BitSet?) : PreparedExit {
        fun allows(target: Int): Boolean = allowed?.get(target) ?: true
    }
    class Terminal(val exit: PortId) : PreparedExit
}

/** Immutable layout/liveness inputs only; no actor, mutable entry or callback is retained. */
internal class PreparedExitDirectory(
    private val layout: MethodBlockLayout,
    private val routes: Map<PortId, MethodBlockRoute>,
    private val backward: Boolean,
    private val live: BlockLiveLocals?,
    private val endpoints: Set<Int>,
    private val originalEntry: Int,
) {
    private data class Key(val scope: BlockScope, val exit: PortId, val base: AccessPathBase)
    private val prepared = HashMap<Key, PreparedExit>()
    private val allowedTargets = HashMap<Int, BitSet>()
    var preparations: Long = 0; private set
    var targetMaskBuilds: Long = 0; private set

    fun getOrPrepare(scope: BlockScope, exit: PortId, base: AccessPathBase): PreparedExit =
        prepared.getOrPut(Key(scope, exit, base)) {
            preparations++
            val block = layout[scope.block]
            if (block.isLeaf && !block.isLoop && block.instructions.isEmpty() && exit.ordinal < 0) {
                // Starts are mutable reachability state, not a frozen destination list.
                val local = base as? AccessPathBase.LocalVar
                PreparedExit.ActualStarts(local?.let { l -> allowedTargets.getOrPut(l.idx) {
                    targetMaskBuilds++
                    BitSet(layout.instructionCount).apply {
                        for (target in 0 until layout.instructionCount) if (keep(target, l.idx)) set(target)
                    }
                } })
            } else if (exit.ordinal < 0) PreparedExit.Terminal(exit)
            else {
                val physical = layout.normalExit(exit)?.routes?.map { id ->
                    checkNotNull(routes[id]) { "A normal interface keeps every native directed route" }
                } ?: routes[exit]?.let(::listOf)
                // Unknown/synthetic interfaces retain their native dispatch/error behavior.
                if (physical == null) PreparedExit.Terminal(exit)
                else {
                    val local = base as? AccessPathBase.LocalVar
                    val kept = if (local == null) physical else physical.filter { keep(it.to, local.idx) }
                    if (kept.isEmpty()) PreparedExit.DeadData else PreparedExit.Routes(kept)
                }
            }
        }

    private fun keep(target: Int, local: Int): Boolean = target == originalEntry || target in endpoints ||
        live?.mayEnter(backward, target, local) != false

    fun clear() { prepared.clear(); allowedTargets.clear() }
}
