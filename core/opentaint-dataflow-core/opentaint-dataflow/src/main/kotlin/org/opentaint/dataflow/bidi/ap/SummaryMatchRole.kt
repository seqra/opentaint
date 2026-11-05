package org.opentaint.dataflow.bidi.ap

/** The supplying relation's origin, independent of native record query semantics. */
enum class SummaryMatchRole {
    CURRENT,
    SAVED_DIRECT,
    OPPOSITE_RECORD,
}
