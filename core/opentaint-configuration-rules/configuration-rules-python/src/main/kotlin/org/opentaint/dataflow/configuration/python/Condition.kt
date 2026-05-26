package org.opentaint.dataflow.configuration.python

import org.opentaint.dataflow.configuration.CommonCondition

typealias PIRCondition = CommonCondition<ContainsMark>

data class ContainsMark(val mark: TaintMark, val pos: Position)
