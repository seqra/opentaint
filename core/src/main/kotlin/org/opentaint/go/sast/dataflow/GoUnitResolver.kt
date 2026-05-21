package org.opentaint.go.sast.dataflow

import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.ir.go.api.GoIRFunction

/**
 * Resolves Go functions to IFDS analysis units.
 *
 * Functions whose package import path is in [projectImportPaths] are analyzed as
 * part of the project (a single shared unit); everything else (stdlib, and the
 * rule-targeted source/sink stubs) is treated as external/unknown so taint rules
 * apply at the call site instead of being analyzed through. This mirrors the
 * mapping used by the proven Go `AnalysisTest` (caller package -> SingletonUnit,
 * `test/util` -> UnknownUnit).
 */
class GoUnitResolver(
    private val projectImportPaths: Set<String>,
) : UnitResolver<GoIRFunction> {
    override fun resolve(method: GoIRFunction): UnitType {
        val importPath = method.pkg?.importPath ?: return UnknownUnit
        return if (importPath in projectImportPaths) SingletonUnit else UnknownUnit
    }
}
