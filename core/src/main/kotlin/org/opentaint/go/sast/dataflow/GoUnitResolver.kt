package org.opentaint.go.sast.dataflow

import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.ir.go.api.GoIRFunction

class GoUnitResolver(
    private val projectImportPaths: Set<String>,
) : UnitResolver<GoIRFunction> {
    data class GoPackageUnit(val pkgImportPath: String): UnitType

    override fun resolve(method: GoIRFunction): UnitType {
        val importPath = method.pkg?.importPath ?: return UnknownUnit
        return if (importPath in projectImportPaths) GoPackageUnit(importPath) else UnknownUnit
    }
}
