package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import java.util.concurrent.ConcurrentHashMap

/**
 * The accessors already demanded by answers to a [TaintMarkFieldUnfoldRequest].
 *
 * A request asks one question: is [mark] hidden under the `[any]` of this frame's initial fact?
 * Answering it asks the frame to split that abstraction on the accessors the answerer found. The
 * demand for a question therefore only grows, and an answer that contributes nothing new has not
 * failed to answer -- it has repeated an answer already given.
 *
 * A question is the ASKING frame (the one the request came from, not the one holding this map),
 * the whole fact it asks about and the mark. Nothing coarser is sound: two different facts --
 * siblings such as `arg0.x.*` and `arg0.w.*` -- are different abstractions, and if they shared a
 * question only the one answered first would be split, so which flow is reported would depend on
 * the order the requests happen to be processed in.
 *
 * Keying on the fact alone does not terminate, though. Splitting `arg0.y.*` on `y` produces
 * `arg0.y.y.*`, which ends in `[any]` again, one accessor further down, and re-raises the same
 * question about a new fact. On a self-similar shape -- `CharSequence#content`, or
 * `MapKey`/`MapValue`/`Element` over erased generics, where the type checker has nothing to stop
 * on -- that loop has no fixed point, and each round re-abstracts the whole accumulated fact tree
 * of the base and re-broadcasts a side effect requirement across the asking frame's transitive
 * callers. So an accessor already on the fact's path is never demanded: that split is the loop,
 * not a refinement. It is decided by the fact alone, so it is the same whatever the order, and it
 * bounds every path by the accessors it can hold without repeating one. The precision it costs is
 * a flow that needs the same accessor twice below one abstraction, `arg0.y.y`.
 *
 * One instance per analysed method, held on its
 * [org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext]. A request climbs through many
 * frames, and each frame it passes through filters against its own record -- so two frames are
 * never made to agree about a question, and nothing here is shared across the analysis.
 * `ConcurrentHashMap.newKeySet().add` is still the atomic step, so workers sharing one method's
 * context cannot both be told the same accessor is fresh.
 */
class MarkUnfoldDemand {
    private data class Question(
        /** The frame the request came from, which is not in general the frame holding this map. */
        val method: MethodEntryPoint,
        /** Without exclusions: an answer replaces them, so they are not part of what is asked. */
        val fact: InitialFactAp,
        val mark: Accessor,
    )

    private val demanded = ConcurrentHashMap<Question, MutableSet<Accessor>>()

    /**
     * Records [accessors] as demanded for the question and returns those that were not demanded
     * before and are not on [fact]'s path already. An empty result means this answer repeats one
     * already given, or would only re-raise the question one accessor further down.
     */
    fun demand(
        method: MethodEntryPoint,
        fact: InitialFactAp,
        mark: Accessor,
        accessors: Collection<Accessor>,
    ): List<Accessor> {
        val onPath = fact.getAllAccessors()
        val refining = accessors.filter { it !in onPath }
        if (refining.isEmpty()) return emptyList()

        val question = Question(method, fact.replaceExclusions(ExclusionSet.Empty), mark)
        val alreadyDemanded = demanded.computeIfAbsent(question) { ConcurrentHashMap.newKeySet() }

        return refining.filter { alreadyDemanded.add(it) }
    }
}
