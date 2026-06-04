package org.opentaint.dataflow.configuration.go.serialized

interface ItemInfo

sealed interface GoSerializedItem {
    val info: ItemInfo?
}

data class GoSerializedGlobalSource(
    val pkg: GoNameMatcher,
    val global: GoNameMatcher,
    val condition: GoSerializedCondition?,
    val taint: List<GoSerializedAssignAction>,
    override val info: ItemInfo?,
) : GoSerializedItem

data class GoSerializedFieldSource(
    val field: GoNameMatcher,
    val condition: GoSerializedCondition?,
    val taint: List<GoSerializedAssignAction>,
    override val info: ItemInfo?,
) : GoSerializedItem

sealed interface GoSerializedRule : GoSerializedItem {
    val pkg: GoNameMatcher
    val function: GoNameMatcher

    data class Source(
        override val pkg: GoNameMatcher,
        override val function: GoNameMatcher,
        val condition: GoSerializedCondition?,
        val taint: List<GoSerializedAssignAction>,
        override val info: ItemInfo?,
    ) : GoSerializedRule

    data class Sink(
        override val pkg: GoNameMatcher,
        override val function: GoNameMatcher,
        val condition: GoSerializedCondition?,
        val trackFactsReachAnalysisEnd: List<GoSerializedAssignAction>? = null,
        val id: String? = null,
        val meta: GoSinkMetaData? = null,
        override val info: ItemInfo?,
    ) : GoSerializedRule

    data class PassThrough(
        override val pkg: GoNameMatcher,
        override val function: GoNameMatcher,
        val copy: List<GoSerializedPassAction>,
        override val info: ItemInfo? = null,
    ) : GoSerializedRule

    data class Cleaner(
        override val pkg: GoNameMatcher,
        override val function: GoNameMatcher,
        val condition: GoSerializedCondition? = null,
        val cleans: List<GoSerializedCleanAction>,
        override val info: ItemInfo?,
    ) : GoSerializedRule
}
