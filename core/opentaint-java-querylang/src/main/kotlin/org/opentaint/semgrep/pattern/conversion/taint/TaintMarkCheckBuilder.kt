package org.opentaint.semgrep.pattern.conversion.taint

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition.True
import org.opentaint.semgrep.pattern.Mark.GeneratedMark

interface MarkConditionBuilder<C> {
    fun checkTaintMark(mark: GeneratedMark, pos: PositionBaseWithModifiers): C
    fun checkTaintMarkOnAnyField(mark: GeneratedMark, pos: PositionBaseWithModifiers): C
    fun negate(cond: C): C
    fun and(args: List<C>): C
    fun or(args: List<C>): C
    fun mkTrue(): C
    fun mkFalse(): C
}

data object JavaMarkConditionBuilder : MarkConditionBuilder<SerializedCondition> {
    override fun checkTaintMark(mark: GeneratedMark, pos: PositionBaseWithModifiers) = mark.mkContainsMark(pos)
    override fun checkTaintMarkOnAnyField(mark: GeneratedMark, pos: PositionBaseWithModifiers) =
        mark.mkContainsMarkOnAnyField(pos)
    override fun negate(cond: SerializedCondition) = SerializedCondition.not(cond)
    override fun and(args: List<SerializedCondition>) = SerializedCondition.and(args)
    override fun or(args: List<SerializedCondition>) = serializedConditionOr(args)
    override fun mkTrue(): SerializedCondition = True
    override fun mkFalse(): SerializedCondition = SerializedCondition.mkFalse()
}

sealed interface TaintMarkCheckBuilder {
    fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C

    // Any-field lift of [build]: every mark leaf becomes a "contains on any field" check on the
    // same mark and position; boolean structure is preserved. Used by starred ($X*) sinks so the
    // any-field arm stays coherent with the composed requires marks (same mark, same base).
    fun <C> buildOnAnyField(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C
}

data class TaintMarkLabelCheckBuilder(val label: GeneratedMark) : TaintMarkCheckBuilder {
    override fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.checkTaintMark(label, position)

    override fun <C> buildOnAnyField(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.checkTaintMarkOnAnyField(label, position)
}

data class TaintMarkNotCheckBuilder(val arg: TaintMarkCheckBuilder) : TaintMarkCheckBuilder {
    override fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.negate(arg.build(builder, position))

    override fun <C> buildOnAnyField(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.negate(arg.buildOnAnyField(builder, position))
}

data class TaintMarkAndCheckBuilder(
    val l: TaintMarkCheckBuilder,
    val r: TaintMarkCheckBuilder
) : TaintMarkCheckBuilder {
    override fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.and(listOf(l.build(builder, position), r.build(builder, position)))

    override fun <C> buildOnAnyField(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.and(listOf(l.buildOnAnyField(builder, position), r.buildOnAnyField(builder, position)))
}

data class TaintMarkOrCheckBuilder(
    val l: TaintMarkCheckBuilder,
    val r: TaintMarkCheckBuilder
) : TaintMarkCheckBuilder {
    override fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.or(listOf(l.build(builder, position), r.build(builder, position)))

    override fun <C> buildOnAnyField(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.or(listOf(l.buildOnAnyField(builder, position), r.buildOnAnyField(builder, position)))
}

data object TaintMarkCheckNotRequiredBuilder : TaintMarkCheckBuilder {
    override fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C = builder.mkTrue()

    override fun <C> buildOnAnyField(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.mkTrue()
}

fun TaintMarkCheckBuilder.collectLabels(dst: MutableSet<GeneratedMark>): Set<GeneratedMark> {
    when (this) {
        is TaintMarkCheckNotRequiredBuilder -> {
            // no labels
        }

        is TaintMarkLabelCheckBuilder -> dst.add(label)
        is TaintMarkNotCheckBuilder -> arg.collectLabels(dst)

        is TaintMarkAndCheckBuilder -> {
            l.collectLabels(dst)
            r.collectLabels(dst)
        }

        is TaintMarkOrCheckBuilder -> {
            l.collectLabels(dst)
            r.collectLabels(dst)
        }
    }
    return dst
}
