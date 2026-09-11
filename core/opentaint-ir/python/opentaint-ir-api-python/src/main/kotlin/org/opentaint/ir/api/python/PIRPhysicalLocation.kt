package org.opentaint.ir.api.python

data class PIRPhysicalLocation(
    val lineStart: UInt,
    val lineEnd: UInt,
    val colStart: UInt,
    val colEnd: UInt,
)
