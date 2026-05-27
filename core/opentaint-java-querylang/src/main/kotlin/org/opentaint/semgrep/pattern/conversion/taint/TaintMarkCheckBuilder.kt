package org.opentaint.semgrep.pattern.conversion.taint

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition.True
import org.opentaint.semgrep.pattern.Mark.GeneratedMark

interface MarkConditionBuilder<C> {
    fun checkMark(mark: GeneratedMark, pos: PositionBaseWithModifiers): C
    fun negate(cond: C): C
    fun and(args: List<C>): C
    fun or(args: List<C>): C
    fun mkTrue(): C
    fun mkFalse(): C
}

data object JavaMarkConditionBuilder : MarkConditionBuilder<SerializedCondition> {
    override fun checkMark(mark: GeneratedMark, pos: PositionBaseWithModifiers) = mark.mkContainsMark(pos)
    override fun negate(cond: SerializedCondition) = SerializedCondition.not(cond)
    override fun and(args: List<SerializedCondition>) = SerializedCondition.and(args)
    override fun or(args: List<SerializedCondition>) = serializedConditionOr(args)
    override fun mkTrue(): SerializedCondition = True
    override fun mkFalse(): SerializedCondition = SerializedCondition.mkFalse()
}

sealed interface TaintMarkCheckBuilder {
    fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C
}

data class TaintMarkLabelCheckBuilder(val label: GeneratedMark) : TaintMarkCheckBuilder {
    override fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.checkMark(label, position)
}

data class TaintMarkNotCheckBuilder(val arg: TaintMarkCheckBuilder) : TaintMarkCheckBuilder {
    override fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.negate(arg.build(builder, position))
}

data class TaintMarkAndCheckBuilder(
    val l: TaintMarkCheckBuilder,
    val r: TaintMarkCheckBuilder
) : TaintMarkCheckBuilder {
    override fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.and(listOf(l.build(builder, position), r.build(builder, position)))
}

data class TaintMarkOrCheckBuilder(
    val l: TaintMarkCheckBuilder,
    val r: TaintMarkCheckBuilder
) : TaintMarkCheckBuilder {
    override fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.or(listOf(l.build(builder, position), r.build(builder, position)))
}

data object TaintMarkCheckNotRequiredBuilder : TaintMarkCheckBuilder {
    override fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C = builder.mkTrue()
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
