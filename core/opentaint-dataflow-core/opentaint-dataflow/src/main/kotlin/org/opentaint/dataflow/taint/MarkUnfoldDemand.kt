package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import java.util.concurrent.ConcurrentHashMap

/**
 * The accessors already demanded by answers to a [TaintMarkFieldUnfoldRequest].
 *
 * A request is a question about one abstraction: "is [mark] hidden under the `[any]` of this frame's
 * initial fact?". Answering it asks the frame to split that abstraction on the accessors the answerer
 * found. The demand for a question therefore only grows, and an answer that contributes nothing new
 * has not failed to answer -- it has repeated an answer already given.
 *
 * Contributing an accessor a second time is not a refinement: the split it asks for produces a fact
 * that ends in `[any]` again, one accessor further down, which re-raises the same question. On a
 * self-similar shape -- `CharSequence#content`, or `MapKey`/`MapValue`/`Element` over erased generics,
 * where the type checker has nothing to stop on -- that loop has no fixed point, and each round
 * re-abstracts the whole accumulated fact tree of the base and re-broadcasts a side effect requirement
 * across the asking frame's transitive callers.
 *
 * The question is keyed on the asking frame, the base the abstraction sits on, and the mark -- not on
 * the current refinement of the fact, which is itself the product of earlier answers.
 */
class MarkUnfoldDemand {
    private data class Question(
        val method: MethodEntryPoint,
        val base: AccessPathBase,
        val mark: Accessor,
    )

    private val demanded = ConcurrentHashMap<Question, MutableSet<Accessor>>()

    /**
     * Records [accessors] as demanded for the question and returns those that were not demanded
     * before. An empty result means the demand for this question is already saturated.
     */
    fun newlyDemanded(
        method: MethodEntryPoint,
        base: AccessPathBase,
        mark: Accessor,
        accessors: Collection<Accessor>,
    ): List<Accessor> {
        if (accessors.isEmpty()) return emptyList()

        val question = Question(method, base, mark)
        val alreadyDemanded = demanded.computeIfAbsent(question) { ConcurrentHashMap.newKeySet() }
        return accessors.filter { alreadyDemanded.add(it) }
    }
}
