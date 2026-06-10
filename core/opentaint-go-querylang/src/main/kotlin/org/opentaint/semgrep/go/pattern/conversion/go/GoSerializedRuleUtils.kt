package org.opentaint.semgrep.go.pattern.conversion.go

import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedAssignAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCleanAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.semgrep.pattern.Mark.GeneratedMark

internal fun PositionBase.baseGo(): PositionBaseWithModifiers.BaseOnly = PositionBaseWithModifiers.BaseOnly(this)

internal fun goAnyNameMatcher(): GoNameMatcher = GoNameMatcher.Pattern(".*")

internal fun GoNameMatcher.matchAnything(): Boolean =
    this is GoNameMatcher.Pattern && regex == ".*"

internal fun GeneratedMark.mkGoContainsMark(pos: PositionBaseWithModifiers): GoSerializedCondition.ContainsMark =
    GoSerializedCondition.ContainsMark(taintMarkStr(), pos)

internal fun GeneratedMark.mkGoContainsMarkOnAnyAccessor(pos: PositionBaseWithModifiers): GoSerializedCondition =
    GoSerializedCondition.ContainsMarkOnAnyAccessor(taintMarkStr(), pos)

internal fun GeneratedMark.mkGoAssignMark(pos: PositionBaseWithModifiers): GoSerializedAssignAction =
    GoSerializedAssignAction.Direct(taintMarkStr(), pos)

internal fun GeneratedMark.mkGoAssignMarkOnAnyAccessor(pos: PositionBaseWithModifiers): GoSerializedAssignAction =
    GoSerializedAssignAction.AnyAccessor(taintMarkStr(), pos)

internal fun GeneratedMark.mkGoCleanMark(pos: PositionBaseWithModifiers): GoSerializedCleanAction =
    GoSerializedCleanAction(taintMarkStr(), pos)
