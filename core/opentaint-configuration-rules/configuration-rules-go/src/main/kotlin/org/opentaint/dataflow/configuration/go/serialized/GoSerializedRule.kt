package org.opentaint.dataflow.configuration.go.serialized

sealed interface GoSerializedItem

sealed interface GoSerializedRule : GoSerializedItem {
    val function: GoFunctionMatcher

    data class Source(
        override val function: GoFunctionMatcher,
        val condition: GoSerializedCondition?,
        val taint: List<GoSerializedAssignAction>,
    ) : GoSerializedRule

    data class Sink(
        override val function: GoFunctionMatcher,
        val condition: GoSerializedCondition?,
        val trackFactsReachAnalysisEnd: List<GoSerializedAssignAction>? = null,
        val id: String? = null,
        val meta: GoSinkMetaData? = null,
    ) : GoSerializedRule

    data class PassThrough(
        override val function: GoFunctionMatcher,
        val copy: List<GoSerializedPassAction>,
    ) : GoSerializedRule

    data class Cleaner(
        override val function: GoFunctionMatcher,
        val condition: GoSerializedCondition? = null,
        val cleans: List<GoSerializedCleanAction>,
    ) : GoSerializedRule
}
