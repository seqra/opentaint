package org.opentaint.jvm.sast.sarif

import org.opentaint.common.sast.sarif.DebugFactReachabilitySarifGenerator
import org.opentaint.common.sast.sarif.SarifGenerationOptions
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.jvm.sast.JIRSourceFileResolver
import org.opentaint.jvm.sast.ast.AstSpanResolverProvider

class JirDebugFactReachabilitySarifGenerator(
    options: SarifGenerationOptions,
    sourceFileResolver: JIRSourceFileResolver,
    private val traits: SarifTraits<CommonMethod, CommonInst>,
): DebugFactReachabilitySarifGenerator<IntermediateLocation>(options) {
    private val spanResolver = AstSpanResolverProvider(traits as JIRSarifTraits)
    override val locationResolver = LocationResolver(sourceFileResolver, traits, spanResolver)

    override fun generateFactLocations(statementFacts: Map<CommonInst, Set<FinalFactAp>>): List<IntermediateLocation> {
        val result = mutableListOf<IntermediateLocation>()

        for ((stmt, facts) in statementFacts) {
            result += IntermediateLocation(
                inst = stmt,
                info = getInstructionInfo(stmt),
                kind = "unknown",
                message = "$facts",
                type = LocationType.Simple
            )
        }

        return result
    }

    private fun getInstructionInfo(statement: CommonInst): InstructionInfo = with(traits) {
        InstructionInfo(
            fullyQualified = locationFQN(statement),
            machineName = locationMachineName(statement),
            lineNumber = lineNumber(statement),
        )
    }
}
