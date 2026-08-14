package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.FactAp
import java.util.concurrent.ConcurrentHashMap

data class MethodTaintMarkState<Method>(
    val method: Method,
    val mark: String,
)

data class TaintMarkTransition(
    val inputMark: String,
    val outputMark: String,
)

data class MethodTaintMarkSummaryStats(
    val methods: Int,
    val transitions: Int,
)

internal class MethodTaintMarkReachabilityIndex<Method> {
    private class MethodSummary {
        val inputMarks = ConcurrentHashMap.newKeySet<String>()
        val outputMarks = ConcurrentHashMap.newKeySet<String>()
        val transitions = ConcurrentHashMap.newKeySet<TaintMarkTransition>()
    }

    private val callers = ConcurrentHashMap<Method, MutableSet<Method>>()
    private val callees = ConcurrentHashMap<Method, MutableSet<Method>>()
    private val summaries = ConcurrentHashMap<Method, MethodSummary>()

    fun addCall(caller: Method, callee: Method) {
        callers.computeIfAbsent(callee) { ConcurrentHashMap.newKeySet() }.add(caller)
        callees.computeIfAbsent(caller) { ConcurrentHashMap.newKeySet() }.add(callee)
    }

    fun addSummaryEdges(method: Method, edges: List<Edge>) {
        edges.forEach { edge ->
            when (edge) {
                is Edge.ZeroToZero -> Unit
                is Edge.ZeroToFact -> recordOutput(method, edge.factAp.taintMarks())
                is Edge.FactToFact -> recordTransition(
                    method,
                    edge.initialFactAp.taintMarks(),
                    edge.factAp.taintMarks(),
                )
                is Edge.NDFactToFact -> edge.initialFacts.forEach { initial ->
                    recordTransition(method, initial.taintMarks(), edge.factAp.taintMarks())
                }
            }
        }
    }

    fun clearSummaries() = summaries.clear()

    fun methodsThatCanReach(method: Method): Set<Method> {
        val reachable = hashSetOf(method)
        val pending = ArrayDeque<Method>()
        pending.addLast(method)

        while (pending.isNotEmpty()) {
            val callee = pending.removeFirst()
            for (caller in callers[callee].orEmpty()) {
                if (reachable.add(caller)) pending.addLast(caller)
            }
        }

        return reachable
    }

    fun statesThatCanReach(
        targetMethod: Method,
        targetMarks: Set<String>,
        ruleTransitions: Map<Method, Set<TaintMarkTransition>>,
    ): Set<MethodTaintMarkState<Method>> {
        if (targetMarks.isEmpty()) return emptySet()

        val reverseRuleTransitions = ruleTransitions.mapValues { (_, transitions) ->
            transitions.groupBy({ it.outputMark }, { it.inputMark })
        }
        val reachable = hashSetOf<MethodTaintMarkState<Method>>()
        val pending = ArrayDeque<MethodTaintMarkState<Method>>()
        targetMarks.forEach { mark ->
            val state = MethodTaintMarkState(targetMethod, mark)
            if (reachable.add(state)) pending.addLast(state)
        }

        fun enqueue(method: Method, mark: String) {
            val state = MethodTaintMarkState(method, mark)
            if (reachable.add(state)) pending.addLast(state)
        }

        while (pending.isNotEmpty()) {
            val (method, mark) = pending.removeFirst()
            val summary = summaries[method]

            summary?.transitions?.forEach { transition ->
                if (transition.outputMark == mark) enqueue(method, transition.inputMark)
            }

            reverseRuleTransitions[method]?.get(mark).orEmpty().forEach { inputMark ->
                enqueue(method, inputMark)
            }

            if (mark in summary?.inputMarks.orEmpty()) {
                callers[method].orEmpty().forEach { caller -> enqueue(caller, mark) }
            }

            callees[method].orEmpty().forEach { callee ->
                if (mark in summaries[callee]?.outputMarks.orEmpty()) {
                    enqueue(callee, mark)
                }
            }
        }

        return reachable
    }

    fun stats(): MethodTaintMarkSummaryStats {
        var transitions = 0
        summaries.values.forEach { summary ->
            transitions += summary.transitions.size
        }
        return MethodTaintMarkSummaryStats(summaries.size, transitions)
    }

    private fun recordTransition(method: Method, inputMarks: Set<String>, outputMarks: Set<String>) {
        if (inputMarks.isEmpty() && outputMarks.isEmpty()) return

        val summary = summaries.computeIfAbsent(method) { MethodSummary() }
        summary.inputMarks += inputMarks
        summary.outputMarks += outputMarks
        inputMarks.forEach { inputMark ->
            outputMarks.forEach { outputMark ->
                summary.transitions += TaintMarkTransition(inputMark, outputMark)
            }
        }
    }

    private fun recordOutput(method: Method, outputMarks: Set<String>) {
        if (outputMarks.isEmpty()) return
        summaries.computeIfAbsent(method) { MethodSummary() }.outputMarks += outputMarks
    }

    private fun FactAp.taintMarks(): Set<String> =
        getAllAccessors().filterIsInstanceTo<TaintMarkAccessor, _>(hashSetOf()).mapTo(hashSetOf()) { it.mark }

    // Test-only semantic entry points. They deliberately mirror the information extracted from summary facts.
    internal fun recordExactSummary(method: Method, inputMark: String, outputMark: String) =
        recordTransition(method, setOf(inputMark), setOf(outputMark))

    internal fun recordSummary(method: Method, inputMarks: Set<String>, outputMarks: Set<String>) =
        recordTransition(method, inputMarks, outputMarks)

    internal fun recordInputMark(method: Method, mark: String) {
        summaries.computeIfAbsent(method) { MethodSummary() }.inputMarks += mark
    }

    internal fun recordOutputMark(method: Method, mark: String) {
        summaries.computeIfAbsent(method) { MethodSummary() }.outputMarks += mark
    }
}
