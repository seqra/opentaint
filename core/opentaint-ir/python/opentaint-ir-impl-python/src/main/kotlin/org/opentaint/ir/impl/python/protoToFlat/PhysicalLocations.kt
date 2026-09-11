package org.opentaint.ir.impl.python.protoToFlat

import org.opentaint.ir.api.python.PIRPhysicalLocation
import org.opentaint.ir.impl.python.proto.MypyExprProto
import org.opentaint.ir.impl.python.proto.MypyStmtProto

internal fun MypyStmtProto.toPhysicalLocation(): PIRPhysicalLocation? =
    physicalLocationOf(line, col, endLine, endCol)

internal fun MypyExprProto.toPhysicalLocation(): PIRPhysicalLocation? =
    physicalLocationOf(line, col, endLine, endCol)

private fun physicalLocationOf(line: Int, col: Int, endLine: Int, endCol: Int): PIRPhysicalLocation? {
    if (line < 0 || col < 0 || endLine < 0 || endCol < 0) return null
    if (endLine < line) return null
    if (endLine == line && endCol < col) return null
    return PIRPhysicalLocation(
        lineStart = line.toUInt(),
        lineEnd = endLine.toUInt(),
        colStart = col.toUInt(),
        colEnd = endCol.toUInt(),
    )
}
