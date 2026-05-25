package org.opentaint.dataflow.configuration.go.serialized

sealed interface GoSerializedItem

data class GoSerializedGlobalSource(
    val global: GoNameMatcher,
    val condition: GoSerializedCondition?,
    val taint: List<GoSerializedAssignAction>,
) : GoSerializedItem

sealed interface GoSerializedRule : GoSerializedItem {
    val function: GoNameMatcher

    data class Source(
        override val function: GoNameMatcher,
        val condition: GoSerializedCondition?,
        val taint: List<GoSerializedAssignAction>,
    ) : GoSerializedRule

    data class Sink(
        override val function: GoNameMatcher,
        val condition: GoSerializedCondition?,
        val trackFactsReachAnalysisEnd: List<GoSerializedAssignAction>? = null,
        val id: String? = null,
        val meta: GoSinkMetaData? = null,
    ) : GoSerializedRule

    data class PassThrough(
        override val function: GoNameMatcher,
        val copy: List<GoSerializedPassAction>,
    ) : GoSerializedRule

    data class Cleaner(
        override val function: GoNameMatcher,
        val condition: GoSerializedCondition? = null,
        val cleans: List<GoSerializedCleanAction>,
    ) : GoSerializedRule
}
