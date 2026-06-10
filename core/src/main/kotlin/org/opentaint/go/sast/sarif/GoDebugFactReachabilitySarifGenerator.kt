package org.opentaint.go.sast.sarif

import org.opentaint.common.sast.sarif.DebugFactReachabilitySarifGenerator
import org.opentaint.common.sast.sarif.SarifGenerationOptions
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.jvm.sast.sarif.InstructionInfo
import org.opentaint.jvm.sast.sarif.IntermediateLocation
import org.opentaint.jvm.sast.sarif.LocationType
import java.nio.file.Path

class GoDebugFactReachabilitySarifGenerator(
    options: SarifGenerationOptions,
    sourceRoot: Path?,
): DebugFactReachabilitySarifGenerator<IntermediateLocation>(options) {
    override val locationResolver = GoLocationResolver(sourceRoot)

    override fun generateFactLocations(statementFacts: Map<CommonInst, Set<FinalFactAp>>): List<IntermediateLocation> =
        statementFacts.entries.mapNotNull { toIntermediate(it.key, it.value) }

    private fun toIntermediate(stmt: CommonInst, facts: Set<FinalFactAp>): IntermediateLocation? {
        val goInst = stmt as? GoIRInst ?: return null
        val function = goInst.location.functionBody.function
        val line = goInst.location.position?.line ?: -1
        return IntermediateLocation(
            inst = stmt,
            info = InstructionInfo(
                fullyQualified = function.fullName,
                machineName = function.name,
                lineNumber = line,
            ),
            kind = "unknown",
            message = "$facts",
            type = LocationType.Simple,
        )
    }
}
