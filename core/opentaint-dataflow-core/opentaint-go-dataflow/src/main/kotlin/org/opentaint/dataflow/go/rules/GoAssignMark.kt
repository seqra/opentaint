package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers

data class GoAssignMark(val mark: String, val pos: PositionBaseWithModifiers)
