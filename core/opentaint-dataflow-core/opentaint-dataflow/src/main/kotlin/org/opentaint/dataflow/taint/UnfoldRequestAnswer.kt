package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp

/**
 * A start accessor of a refinement delta that leads to the requested mark, with the length of
 * the shortest path from it down to the mark and the delta below it.
 */
internal class MarkCandidate(
    val accessor: Accessor,
    val depth: Int,
    val successors: FinalFactAp.Delta?,
) {
    private var pathAccessors: Set<Accessor>? = null

    /**
     * The accessors on this candidate's shortest path to [mark], the start accessor and the mark
     * included. What two candidates share here is how much of the same structure they walk, which
     * is how a second answer is chosen to add something the first did not already cover.
     */
    fun pathAccessors(mark: Accessor): Set<Accessor> {
        pathAccessors?.let { return it }

        val path = linkedSetOf(accessor)
        successors?.collectShortestPathTo(mark, path)

        return path.also { pathAccessors = it }
    }
}

/**
 * Every start accessor of this delta that leads to [mark], each with the distance from it down
 * to the mark.
 *
 * `[any]` is not something the asking frame can unfold on -- it is the abstraction the request
 * is asking to see through -- so an `[any]` start accessor contributes its own successors
 * instead, at the depth they sit at below it.
 */
internal fun FinalFactAp.Delta.markCandidates(mark: Accessor): List<MarkCandidate> {
    val candidates = mutableListOf<MarkCandidate>()

    fun consider(accessor: Accessor, successors: FinalFactAp.Delta?) {
        val depth = when {
            accessor == mark -> 1
            successors == null -> return
            else -> successors.minDepthToAccessor(mark).let { if (it < 0) return else it + 1 }
        }

        candidates.add(MarkCandidate(accessor, depth, successors))
    }

    for (accessor in getStartAccessors()) {
        if (accessor != AnyAccessor) {
            consider(accessor, readAccessor(accessor))
            continue
        }

        val anyNode = readAccessor(accessor) ?: continue
        for (successor in anyNode.getStartAccessors()) {
            if (successor == AnyAccessor) continue
            consider(successor, anyNode.readAccessor(successor))
        }
    }

    return candidates
}

/**
 * Which accessors to answer an unfold request with, out of the places the mark may be.
 *
 * Answering with all of them is the complete answer, and it is also what makes the request
 * multiply: each accessor in the answer becomes an exclusion at the asking frame, each exclusion
 * spawns an abstraction there, and each abstraction raises unfold requests of its own -- so the
 * candidate count is a branching factor applied once per frame the demand passes through.
 *
 * The first answer is therefore the candidate whose mark is nearest, and the least accessor
 * among those that tie -- least in the accessors' own order, which is total, so the choice does
 * not depend on iteration order and the same delta always answers the same way.
 *
 * [extraPaths] more follow, each the candidate that re-walks least of what is already covered,
 * then nearest, then least. Overlap is what makes a second answer worth its cost: a candidate
 * whose path shares nothing with the first reaches structure the first does not, while one that
 * shares most of it is close to a restatement. The caller decides how many to allow, and spends
 * them where a second answer is cheap.
 *
 * Narrowing here is a deliberate loss of precision: a mark reachable only along a path that is
 * neither nearest nor sufficiently disjoint is not unfolded, and a flow that needs it is not
 * reported.
 */
internal fun List<MarkCandidate>.selectAnswer(mark: Accessor, extraPaths: Int): List<Accessor> {
    val first = nearest() ?: return emptyList()
    if (extraPaths <= 0 || size == 1) return listOf(first.accessor)

    val chosen = mutableListOf(first)
    val covered = first.pathAccessors(mark).toMutableSet()

    repeat(extraPaths) {
        val next = filterNot { candidate -> chosen.any { it === candidate } }
            .minWithOrNull(
                compareBy(
                    { candidate -> candidate.pathAccessors(mark).count { it in covered } },
                    { it.depth },
                    { it.accessor }
                )
            ) ?: return chosen.map { it.accessor }

        chosen.add(next)
        covered.addAll(next.pathAccessors(mark))
    }

    return chosen.map { it.accessor }
}

/**
 * Walks one shortest path from here down to [mark], collecting the accessors it steps on into
 * [into], the mark included.
 *
 * Ties are broken by the accessors' own order, and a concrete step is taken over an `[any]` one
 * whenever both reach the mark equally fast -- so the path is a function of the delta rather
 * than of the order its children happen to be enumerated in.
 */
private fun FinalFactAp.Delta.collectShortestPathTo(mark: Accessor, into: MutableSet<Accessor>) {
    var node: FinalFactAp.Delta = this
    val visited = hashSetOf(node)

    while (true) {
        val distance = node.minDepthToAccessor(mark)
        if (distance < 0) return

        var stepAccessor: Accessor? = null
        var step: FinalFactAp.Delta? = null
        var freeStep: FinalFactAp.Delta? = null

        for (accessor in node.getStartAccessors().sorted()) {
            val child = node.readAccessor(accessor) ?: continue

            if (accessor == AnyAccessor) {
                // `[any]` consumes nothing, so it reaches the mark at the same distance
                if (freeStep == null && child.minDepthToAccessor(mark) == distance) freeStep = child
                continue
            }

            if (accessor == mark && distance == 1) {
                into.add(mark)
                return
            }

            if (child.minDepthToAccessor(mark) == distance - 1) {
                stepAccessor = accessor
                step = child
                break
            }
        }

        val next = step ?: freeStep ?: return
        if (!visited.add(next)) return

        stepAccessor?.let { into.add(it) }
        node = next
    }
}

/**
 * The nearest mark, and the least accessor among those that reach it equally near.
 */
internal fun List<MarkCandidate>.nearest(): MarkCandidate? {
    var best: MarkCandidate? = null

    for (candidate in this) {
        val current = best
        val better = current == null ||
            candidate.depth < current.depth ||
            (candidate.depth == current.depth && candidate.accessor < current.accessor)

        if (better) best = candidate
    }

    return best
}
