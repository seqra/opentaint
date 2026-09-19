package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import java.util.concurrent.ConcurrentHashMap

/**
 * The accessors already demanded by answers to a [TaintMarkFieldUnfoldRequest].
 *
 * A request is a question about one abstraction: "is [mark] hidden under the `[any]` of this
 * frame's initial fact?". Answering it asks the frame to split that abstraction on the accessors
 * the answerer found. The demand for a question therefore only grows, and an answer that
 * contributes nothing new has not failed to answer -- it has repeated an answer already given.
 *
 * Contributing an accessor a second time is not a refinement: the split it asks for produces a
 * fact that ends in `[any]` again, one accessor further down, which re-raises the same question.
 * On a self-similar shape -- `CharSequence#content`, or `MapKey`/`MapValue`/`Element` over erased
 * generics, where the type checker has nothing to stop on -- that loop has no fixed point, and
 * each round re-abstracts the whole accumulated fact tree of the base and re-broadcasts a side
 * effect requirement across the asking frame's transitive callers.
 *
 * The question is keyed on the asking frame, the base the abstraction sits on, and the mark --
 * NOT on the current refinement of the fact, which is itself the product of earlier answers.
 * One instance per analysis, shared by every worker. [alreadyDemanded] and [demand] are not one
 * atomic step, so two workers can both find an accessor fresh and both answer with it -- the
 * summary storage keys on the requirement and collapses the pair, so the race costs a duplicate
 * post and nothing else.
 *
 * That is where the precision goes: `arg0.*` and `arg0.x.*` are the same question here, so a
 * frame that has already been asked to split on `x` is not asked again one level down, and a
 * flow that needs `arg0.x.x` is not reported. Keying on the refinement instead makes every
 * iteration its own question and the filter a no-op, which is exactly the loop it is here to cut.
 */
class MarkUnfoldDemand {
    private data class Question(
        val method: MethodEntryPoint,
        val base: AccessPathBase,
        val mark: Accessor,
    )

    private val demanded = ConcurrentHashMap<Question, MutableSet<Accessor>>()

    private fun accessorsFor(method: MethodEntryPoint, base: AccessPathBase, mark: Accessor) =
        demanded.computeIfAbsent(Question(method, base, mark)) { ConcurrentHashMap.newKeySet() }

    /**
     * Whether [accessor] has already been demanded for this question, without recording it.
     *
     * Asked before the answer is chosen, so a stale candidate is passed over rather than
     * consuming the whole answer: the two narrowings -- this one and the nearest-first
     * selection -- would otherwise compound, and the nearest candidate being stale would hide a
     * fresh one behind it.
     */
    fun alreadyDemanded(
        method: MethodEntryPoint,
        base: AccessPathBase,
        mark: Accessor,
        accessor: Accessor,
    ): Boolean = accessorsFor(method, base, mark).contains(accessor)

    /**
     * Records [accessors] as demanded for the question and returns those that were not demanded
     * before. An empty result means this answer repeats one already given.
     */
    fun demand(
        method: MethodEntryPoint,
        base: AccessPathBase,
        mark: Accessor,
        accessors: Collection<Accessor>,
    ): List<Accessor> {
        if (accessors.isEmpty()) return emptyList()

        val alreadyDemanded = accessorsFor(method, base, mark)
        return accessors.filter { alreadyDemanded.add(it) }
    }
}
