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

// Lifts a plain [MarkConditionBuilder] into its any-field form: the mark leaf ([checkTaintMark])
// is rerouted to [checkTaintMarkOnAnyField], while boolean structure (negate/and/or/true/false) is
// delegated unchanged. This is the single source of the plain -> any-field mapping, guaranteeing the
// plain and any-field arms carry the SAME mark on the SAME base, differing only ContainsMark vs
// ContainsMarkOnAnyField. Impls are stateless singletons, so delegation via `by inner` is sound.
class AnyFieldLift<C>(private val inner: MarkConditionBuilder<C>) : MarkConditionBuilder<C> by inner {
    override fun checkTaintMark(mark: GeneratedMark, pos: PositionBaseWithModifiers): C =
        inner.checkTaintMarkOnAnyField(mark, pos)
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
    // Defined once by lifting the builder ([AnyFieldLift]) rather than mirroring [build] per case,
    // so a subclass that overrides only [build] cannot desync its any-field arm.
    fun <C> buildOnAnyField(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        build(AnyFieldLift(builder), position)
}

data class TaintMarkLabelCheckBuilder(val label: GeneratedMark) : TaintMarkCheckBuilder {
    override fun <C> build(builder: MarkConditionBuilder<C>, position: PositionBaseWithModifiers): C =
        builder.checkTaintMark(label, position)
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
