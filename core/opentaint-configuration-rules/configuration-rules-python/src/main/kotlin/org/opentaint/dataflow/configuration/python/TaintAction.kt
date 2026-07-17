package org.opentaint.dataflow.configuration.python

import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintAssignAction

/**
 * In-memory counterparts of the `taint:` / `cleans:` / `copy:` action entries
 * declared in [org.opentaint.dataflow.configuration.python.serialized]. Two
 * structural changes vs. the serialized form:
 *  - `kind` / `taintKind` are materialized into a [TaintMark] (interned at
 *    config load time);
 *  - positions are converted to the local [Position] model, which makes the
 *    `arg(*)` wildcard a distinct [PositionBase.AllArguments] case.
 *
 * Decorator / base-class predicates never reach this model: the resolver compiles
 * against one concrete `PIRFunction`, so it folds them to a `true` / `false` literal
 * at conversion time — the same way the JVM discharges `MethodAnnotated`.
 */

sealed interface Action: CommonTaintAction

data class TaintAssignAction(
    val mark: TaintMark,
    val pos: Position,
) : Action, CommonTaintAssignAction

/** `cleans:` entry on cleaner rules — removes [mark] at [pos]. */
data class TaintCleanAction(
    val mark: TaintMark,
    val pos: Position,
) : Action

/** `copy:` entry on passThrough rules. A null [mark] propagates every mark. */
data class TaintPassAction(
    val mark: TaintMark?,
    val from: Position,
    val to: Position,
) : Action
