package org.opentaint.common.sast.dataflow

import org.opentaint.dataflow.ap.ifds.trace.action.ActionableRulesCollectionResult

internal fun actionableRulesWithFallback(
    searchResults: List<ActionableRulesCollectionResult>,
    fallback: (unprocessedIndices: List<Int>) -> ActionableRulesCollectionResult.Collected?,
): List<ActionableRulesCollectionResult.Collected> {
    val collected = searchResults
        .filterIsInstance<ActionableRulesCollectionResult.Collected>()
        .toMutableList()
    val unprocessedIndices = searchResults.indices.filter { index ->
        searchResults[index] === ActionableRulesCollectionResult.Unprocessed
    }
    if (unprocessedIndices.isEmpty()) return collected

    fallback(unprocessedIndices)?.let(collected::add)
    return collected
}
