package org.opentaint.dataflow.ap.ifds.trace.path

import org.opentaint.dataflow.ap.ifds.MethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp.Delta
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.ActionVariant
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry.SourceStartEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction.TraceSummaryEdge
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.InterProceduralMethodEntryNode
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.InterProceduralStart2FinalTraceNode
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.InterProceduralSummaryTraceNode
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.InterProceduralTraceNode
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.ir.api.common.CommonMethod

/** Ordering fallback for leaf domain values that expose no structural comparator. */
private object LeafTextComparator : Comparator<Any> {
    override fun compare(a: Any, b: Any): Int = a.toString().compareTo(b.toString())
}

object MethodContextComparator : Comparator<MethodContext> {
    override fun compare(a: MethodContext, b: MethodContext): Int = LeafTextComparator.compare(a, b)
}

object TraceFactComparator : Comparator<InitialFactAp> {
    override fun compare(a: InitialFactAp, b: InitialFactAp): Int = LeafTextComparator.compare(a, b)
}

object FactDeltaComparator : Comparator<Delta> {
    override fun compare(a: Delta, b: Delta): Int = LeafTextComparator.compare(a, b)
}

object TaintRuleComparator : Comparator<CommonTaintConfigurationItem> {
    override fun compare(a: CommonTaintConfigurationItem, b: CommonTaintConfigurationItem): Int =
        LeafTextComparator.compare(a, b)
}

object TaintActionComparator : Comparator<CommonTaintAction> {
    override fun compare(a: CommonTaintAction, b: CommonTaintAction): Int = LeafTextComparator.compare(a, b)
}

object CommonMethodComparator : Comparator<CommonMethod> {
    override fun compare(a: CommonMethod, b: CommonMethod): Int = LeafTextComparator.compare(a, b)
}

object MethodComparator : Comparator<MethodEntryPoint> {
    override fun compare(a: MethodEntryPoint, b: MethodEntryPoint): Int =
        CommonMethodComparator.compare(a.method, b.method).ifEqual {
            a.statement.location.index.compareTo(b.statement.location.index).ifEqual {
                MethodContextComparator.compare(a.context, b.context)
            }
        }
}

object TraceEdgeComparator : Comparator<MethodTraceResolver.TraceEdge> {
    override fun compare(a: MethodTraceResolver.TraceEdge, b: MethodTraceResolver.TraceEdge): Int =
        edgeKind(a).compareTo(edgeKind(b)).ifEqual {
            when (a) {
                is MethodTraceResolver.TraceEdge.SourceTraceEdge -> {
                    b as MethodTraceResolver.TraceEdge.SourceTraceEdge
                    TraceFactComparator.compare(a.fact, b.fact)
                }
                is MethodTraceResolver.TraceEdge.MethodTraceEdge -> {
                    b as MethodTraceResolver.TraceEdge.MethodTraceEdge
                    TraceFactComparator.compare(a.initialFact, b.initialFact).ifEqual {
                        TraceFactComparator.compare(a.fact, b.fact)
                    }
                }
                is MethodTraceResolver.TraceEdge.MethodTraceNDEdge -> {
                    b as MethodTraceResolver.TraceEdge.MethodTraceNDEdge
                    TraceFactComparator.compareUnordered(a.initialFacts, b.initialFacts).ifEqual {
                        TraceFactComparator.compare(a.fact, b.fact)
                    }
                }
            }
        }

    private fun edgeKind(edge: MethodTraceResolver.TraceEdge): Int = when (edge) {
        is MethodTraceResolver.TraceEdge.SourceTraceEdge -> 0
        is MethodTraceResolver.TraceEdge.MethodTraceEdge -> 1
        is MethodTraceResolver.TraceEdge.MethodTraceNDEdge -> 2
    }
}

object SummaryTraceComparator : Comparator<MethodTraceResolver.SummaryTrace> {
    override fun compare(a: MethodTraceResolver.SummaryTrace, b: MethodTraceResolver.SummaryTrace): Int =
        MethodComparator.compare(a.method, b.method).ifEqual {
            a.traceKind.compareTo(b.traceKind).ifEqual {
                FinalEntryComparator.compare(a.final, b.final)
            }
        }
}

object TraceSummaryEdgeComparator : Comparator<TraceSummaryEdge> {
    override fun compare(a: TraceSummaryEdge, b: TraceSummaryEdge): Int =
        summaryEdgeKind(a).compareTo(summaryEdgeKind(b)).ifEqual {
            TraceEdgeComparator.compare(a.edge, b.edge).ifEqual {
                TraceEdgeComparator.compare(a.edgeAfter, b.edgeAfter).ifEqual {
                    if (a !is TraceSummaryEdge.MethodSummary) {
                        return@ifEqual 0
                    }

                    b as TraceSummaryEdge.MethodSummary
                    compareNullable(a.delta, b.delta) { ad, bd ->
                        TraceFactComparator.compare(ad.initialFact, bd.initialFact).ifEqual {
                            FactDeltaComparator.compare(ad.delta, bd.delta)
                        }
                    }
                }
            }
        }

    private fun summaryEdgeKind(edge: TraceSummaryEdge): Int = when (edge) {
        is TraceSummaryEdge.SourceSummary -> 0
        is TraceSummaryEdge.MethodSummary -> 1
    }
}

object TraceEntryActionComparator : Comparator<TraceEntryAction> {
    override fun compare(a: TraceEntryAction, b: TraceEntryAction): Int =
        actionKind(a).compareTo(actionKind(b)).ifEqual {
            when (a) {
                is TraceEntryAction.Sequential -> {
                    b as TraceEntryAction.Sequential
                    compareEdges(a.edges, b.edges).ifEqual { compareEdges(a.edgesAfter, b.edgesAfter) }
                }
                is TraceEntryAction.SequentialSourceRule -> {
                    b as TraceEntryAction.SequentialSourceRule
                    compareEdges(a.sourceEdges, b.sourceEdges).ifEqual {
                        TaintRuleComparator.compare(a.rule, b.rule).ifEqual {
                            TaintActionComparator.compareUnordered(a.action, b.action)
                        }
                    }
                }
                is TraceEntryAction.CallSourceRule -> compareCallRule(a, b as TraceEntryAction.CallSourceRule)
                is TraceEntryAction.EntryPointSourceRule -> {
                    b as TraceEntryAction.EntryPointSourceRule
                    compareEdges(a.sourceEdges, b.sourceEdges).ifEqual {
                        MethodComparator.compare(a.entryPoint, b.entryPoint).ifEqual {
                            TaintRuleComparator.compare(a.rule, b.rule).ifEqual {
                                TaintActionComparator.compareUnordered(a.action, b.action)
                            }
                        }
                    }
                }
                is TraceEntryAction.CallRule -> {
                    b as TraceEntryAction.CallRule
                    compareEdges(a.edges, b.edges)
                        .ifEqual { compareEdges(a.edgesAfter, b.edgesAfter) }
                        .ifEqual {
                            TaintRuleComparator.compare(a.rule, b.rule).ifEqual {
                                TaintActionComparator.compareUnordered(a.action, b.action)
                            }
                        }
                }
                is TraceEntryAction.CallSummary -> {
                    b as TraceEntryAction.CallSummary
                    compareSummaryEdges(a.summaryEdges, b.summaryEdges).ifEqual {
                        SummaryTraceComparator.compare(a.summaryTrace, b.summaryTrace)
                    }
                }
                is TraceEntryAction.CallSourceSummary -> {
                    b as TraceEntryAction.CallSourceSummary
                    compareSummaryEdges(a.summaryEdges, b.summaryEdges).ifEqual {
                        SummaryTraceComparator.compare(a.summaryTrace, b.summaryTrace)
                    }
                }
                is TraceEntryAction.UnresolvedCallSkip -> {
                    b as TraceEntryAction.UnresolvedCallSkip
                    compareEdges(a.edges, b.edges).ifEqual { compareEdges(a.edgesAfter, b.edgesAfter) }
                }
            }
        }

    private fun compareCallRule(a: TraceEntryAction.CallSourceRule, b: TraceEntryAction.CallSourceRule): Int =
        compareEdges(a.sourceEdges, b.sourceEdges).ifEqual {
            TaintRuleComparator.compare(a.rule, b.rule).ifEqual {
                TaintActionComparator.compareUnordered(a.action, b.action)
            }
        }

    private fun compareEdges(a: Collection<MethodTraceResolver.TraceEdge>, b: Collection<MethodTraceResolver.TraceEdge>) =
        TraceEdgeComparator.compareUnordered(a, b)

    private fun compareSummaryEdges(
        a: Collection<TraceSummaryEdge>,
        b: Collection<TraceSummaryEdge>,
    ) = TraceSummaryEdgeComparator.compareUnordered(a, b)

    private fun actionKind(action: TraceEntryAction): Int = when (action) {
        is TraceEntryAction.Sequential -> 0
        is TraceEntryAction.SequentialSourceRule -> 1
        is TraceEntryAction.CallSourceRule -> 2
        is TraceEntryAction.EntryPointSourceRule -> 3
        is TraceEntryAction.CallRule -> 4
        is TraceEntryAction.CallSummary -> 5
        is TraceEntryAction.CallSourceSummary -> 6
        is TraceEntryAction.UnresolvedCallSkip -> 7
    }
}

object TraceEntryComparator : Comparator<TraceEntry> {
    override fun compare(a: TraceEntry, b: TraceEntry): Int =
        entryKind(a).compareTo(entryKind(b)).ifEqual {
            // Entries in one intra-procedural trace necessarily belong to the same method.
            a.statement.location.index.compareTo(b.statement.location.index).ifEqual {
                TraceEdgeComparator.compareUnordered(a.edges, b.edges).ifEqual {
                    when (a) {
                        is TraceEntry.MethodEntry -> {
                            b as TraceEntry.MethodEntry
                            MethodContextComparator.compare(a.entryPoint.context, b.entryPoint.context).ifEqual {
                                TraceFactComparator.compareUnordered(a.facts, b.facts)
                            }
                        }
                        is SourceStartEntry -> {
                            b as SourceStartEntry
                            compareNullable(a.sourcePrimaryAction, b.sourcePrimaryAction, TraceEntryActionComparator::compare).ifEqual {
                                TraceEntryActionComparator.compareUnordered(a.sourceOtherActions, b.sourceOtherActions)
                            }
                        }
                        else -> 0
                    }
                }
            }
        }

    private fun entryKind(entry: TraceEntry): Int = when (entry) {
        is TraceEntry.MethodEntry -> 0
        is SourceStartEntry -> 1
        is TraceEntry.Action -> 2
        is TraceEntry.Unchanged -> 3
        is TraceEntry.Final -> 4
    }
}

object FinalEntryComparator : Comparator<TraceEntry.Final> {
    override fun compare(a: TraceEntry.Final, b: TraceEntry.Final): Int = TraceEntryComparator.compare(a, b)
}

object StartEntryComparator : Comparator<TraceEntry.StartTraceEntry> {
    override fun compare(a: TraceEntry.StartTraceEntry, b: TraceEntry.StartTraceEntry): Int = when (a) {
        is SourceStartEntry -> when (b) {
            is SourceStartEntry -> a.priority().compareTo(b.priority()).ifEqual { TraceEntryComparator.compare(a, b) }
            is TraceEntry.MethodEntry -> -1
        }
        is TraceEntry.MethodEntry -> when (b) {
            is SourceStartEntry -> 1
            is TraceEntry.MethodEntry -> TraceEntryComparator.compare(a, b)
        }
    }
}

fun SourceStartEntry.priority(): Int {
    if (sourcePrimaryAction != null) return 2
    if (sourceOtherActions.any { it is TraceEntryAction.EntryPointSourceRule }) return 0
    if (sourceOtherActions.any { it is TraceEntryAction.CallSourceRule }) return 1
    return 3
}

object FullTraceComparator : Comparator<MethodTraceResolver.FullStart2FinalTrace> {
    override fun compare(a: MethodTraceResolver.FullStart2FinalTrace, b: MethodTraceResolver.FullStart2FinalTrace): Int =
        a.traceKind.compareTo(b.traceKind).ifEqual {
            TraceEntryComparator.compare(a.startEntry, b.startEntry).ifEqual {
                FinalEntryComparator.compare(a.final, b.final)
            }
        }
}

object ActionVariantComparator : Comparator<ActionVariant> {
    override fun compare(a: ActionVariant, b: ActionVariant): Int =
        compareNullable(a.primaryAction, b.primaryAction, TraceEntryActionComparator::compare).ifEqual {
            TraceEntryActionComparator.compareUnordered(a.otherActions, b.otherActions).ifEqual {
                TraceEdgeComparator.compareUnordered(a.unchanged, b.unchanged)
            }
        }
}

fun MethodTraceResolver.FullStart2FinalTrace.compareEntryIds(a: Int, b: Int): Int {
    val ae = entries[a]
    val be = entries[b]
    return TraceEntryComparator.compare(ae, be).ifEqual {
        if (ae !is TraceEntry.Action || be !is TraceEntry.Action) return@ifEqual 0
        ActionVariantComparator.compareUnordered(actionVariants.get(a).orEmpty(), actionVariants.get(b).orEmpty())
    }
}

object NodeComparator : Comparator<InterProceduralTraceNode> {
    override fun compare(a: InterProceduralTraceNode, b: InterProceduralTraceNode): Int = when (a) {
        is InterProceduralSummaryTraceNode -> when (b) {
            is InterProceduralSummaryTraceNode -> SummaryNodeComparator.compare(a, b)
            is InterProceduralMethodEntryNode,
            is InterProceduralStart2FinalTraceNode -> -1
        }
        is InterProceduralMethodEntryNode -> when (b) {
            is InterProceduralSummaryTraceNode -> 1
            is InterProceduralMethodEntryNode -> MethodEntryNodeComparator.compare(a, b)
            is InterProceduralStart2FinalTraceNode -> -1
        }
        is InterProceduralStart2FinalTraceNode -> when (b) {
            is InterProceduralSummaryTraceNode,
            is InterProceduralMethodEntryNode -> 1
            is InterProceduralStart2FinalTraceNode -> FullNodeComparator.compare(a, b)
        }
    }
}

object MethodEntryNodeComparator : Comparator<InterProceduralMethodEntryNode> {
    override fun compare(a: InterProceduralMethodEntryNode, b: InterProceduralMethodEntryNode): Int =
        MethodComparator.compare(a.entry.entryPoint, b.entry.entryPoint).ifEqual {
            TraceFactComparator.compareUnordered(a.entry.facts, b.entry.facts)
        }
}

object SummaryNodeComparator : Comparator<InterProceduralSummaryTraceNode> {
    override fun compare(a: InterProceduralSummaryTraceNode, b: InterProceduralSummaryTraceNode): Int =
        MethodComparator.compare(a.trace.method, b.trace.method).ifEqual {
            a.trace.traceKind.compareTo(b.trace.traceKind).ifEqual {
                FinalEntryComparator.compare(a.trace.final, b.trace.final)
            }
        }
}

object FullNodeComparator : Comparator<InterProceduralStart2FinalTraceNode> {
    override fun compare(a: InterProceduralStart2FinalTraceNode, b: InterProceduralStart2FinalTraceNode): Int =
        MethodComparator.compare(a.trace.method, b.trace.method).ifEqual {
            a.trace.traceKind.compareTo(b.trace.traceKind).ifEqual {
                FinalEntryComparator.compare(a.trace.final, b.trace.final).ifEqual {
                    StartEntryComparator.compare(a.trace.startEntry, b.trace.startEntry)
                }
            }
        }
}

private inline fun Int.ifEqual(next: () -> Int): Int = if (this != 0) this else next()

private fun <T> compareNullable(a: T?, b: T?, compare: (T, T) -> Int): Int = when {
    a == null -> if (b == null) 0 else -1
    b == null -> 1
    else -> compare(a, b)
}

private fun <T> Comparator<in T>.compareIterables(a: Iterable<T>, b: Iterable<T>): Int {
    val ai = a.iterator()
    val bi = b.iterator()
    while (ai.hasNext() && bi.hasNext()) {
        compare(ai.next(), bi.next()).let { if (it != 0) return it }
    }
    return ai.hasNext().compareTo(bi.hasNext())
}

private fun <T> Comparator<in T>.compareUnordered(a: Iterable<T>, b: Iterable<T>): Int =
    compareIterables(a.sortedWith(this), b.sortedWith(this))
