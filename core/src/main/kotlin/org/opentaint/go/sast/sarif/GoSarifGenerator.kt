package org.opentaint.go.sast.sarif

import org.opentaint.common.sast.sarif.SarifGenerationOptions
import org.opentaint.common.sast.sarif.SarifGenerator
import org.opentaint.common.sast.sarif.TracePathNode
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.inst.GoInstLocation
import org.opentaint.jvm.sast.sarif.InstructionInfo
import org.opentaint.jvm.sast.sarif.IntermediateLocation
import org.opentaint.jvm.sast.sarif.LocationType
import java.nio.file.Path
import java.security.MessageDigest

class GoSarifGenerator(
    options: SarifGenerationOptions,
    sourceRoot: Path?,
): SarifGenerator<IntermediateLocation>(options, sourceRoot) {
    override val locationResolver = GoLocationResolver(sourceRoot)

    override fun generateThreadFlow(
        path: List<TracePathNode>,
        sinkMessage: String
    ): List<IntermediateLocation> {
        val messageBuilder = GoTraceMessageBuilder(sinkMessage)
        return path.mapNotNull { node -> flowLocation(node, messageBuilder) }
    }

    override fun vulnerabilityLocation(
        vulnerability: TaintSinkTracker.TaintVulnerability,
        threadFlows: List<List<IntermediateLocation>>?
    ): IntermediateLocation? {
        return goStatementLocation(vulnerability.statement)
    }

    override fun MessageDigest.addLocationFingerprint(loc: IntermediateLocation) {
        val instLoc = loc.inst.location as? GoInstLocation ?: return
        update(instLoc.functionBody.function.fullName.toByteArray())
        update(instLoc.index.toString().toByteArray())
    }

    private fun flowLocation(node: TracePathNode, messageBuilder: GoTraceMessageBuilder): IntermediateLocation? {
        val inst = node.statement as? GoIRInst ?: return null
        // Drop steps with no source position to avoid meaningless SARIF regions.
        if (inst.location.position == null) return null
        return IntermediateLocation(
            inst = inst,
            info = instructionInfo(inst),
            kind = messageBuilder.sarifKind(node),
            message = messageBuilder.messageFor(node),
            type = LocationType.Simple,
        )
    }

    private fun goStatementLocation(statement: CommonInst): IntermediateLocation? {
        val inst = statement as? GoIRInst ?: return null
        return IntermediateLocation(
            inst = inst,
            info = instructionInfo(inst),
            kind = "taint",
            message = null,
            type = LocationType.Simple,
        )
    }

    private fun instructionInfo(inst: GoIRInst): InstructionInfo {
        val function = inst.location.functionBody.function
        val line = inst.location.position?.line ?: -1
        return InstructionInfo(
            fullyQualified = function.fullName,
            machineName = function.name,
            lineNumber = line,
        )
    }
}
