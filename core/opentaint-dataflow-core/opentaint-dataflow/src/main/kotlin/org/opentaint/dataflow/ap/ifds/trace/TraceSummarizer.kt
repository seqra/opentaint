package org.opentaint.dataflow.ap.ifds.trace

/**
 * Collects caller-defined metadata about entries discovered during intra-procedural trace resolution.
 *
 * The resolver reports every structurally unique entry once, in an unspecified discovery order. The
 * summarizer owns its mutable state and its lifetime: reusing one instance across resolver calls
 * accumulates metadata across those calls. Implementations do not need to be thread-safe unless the
 * caller shares an instance between concurrently used resolvers.
 *
 * Discovered entries can include entries that are later removed as unreachable from a requested
 * start-to-final trace.
 */
fun interface TraceSummarizer {
    fun summarizeTraceEntry(entry: MethodTraceResolver.TraceEntry)
}

data class TraceMetadata(
    val requiresFullTraceResolution: Boolean,
) {
    fun merge(other: TraceMetadata): TraceMetadata = TraceMetadata(
        requiresFullTraceResolution = requiresFullTraceResolution || other.requiresFullTraceResolution,
    )

    companion object {
        val Unknown = TraceMetadata(requiresFullTraceResolution = true)
    }
}

class TraceMetadataSummarizer : TraceSummarizer {
    private var requiresFullTraceResolution = false

    override fun summarizeTraceEntry(entry: MethodTraceResolver.TraceEntry) {
        requiresFullTraceResolution = requiresFullTraceResolution || entry.requiresFullTraceResolution()
    }

    fun metadata(): TraceMetadata = TraceMetadata(requiresFullTraceResolution)

    private fun MethodTraceResolver.TraceEntry.requiresFullTraceResolution(): Boolean = when (this) {
        is MethodTraceResolver.TraceEntry.Action -> true
        is MethodTraceResolver.TraceEntry.SourceStartEntry -> true

        is MethodTraceResolver.TraceEntry.Final,
        is MethodTraceResolver.TraceEntry.MethodEntry,
        is MethodTraceResolver.TraceEntry.Unchanged -> false
    }
}
