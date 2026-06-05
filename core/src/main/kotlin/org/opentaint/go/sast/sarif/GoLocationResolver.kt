package org.opentaint.go.sast.sarif

import io.github.detekt.sarif4k.ArtifactLocation
import io.github.detekt.sarif4k.Location
import io.github.detekt.sarif4k.LogicalLocation
import io.github.detekt.sarif4k.Message
import io.github.detekt.sarif4k.PhysicalLocation
import io.github.detekt.sarif4k.Region
import io.github.detekt.sarif4k.ThreadFlowLocation
import org.opentaint.common.sast.sarif.SarifGenerationOptions
import org.opentaint.common.sast.sarif.SarifLocationResolver
import org.opentaint.ir.go.api.GoIRPosition
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.jvm.sast.sarif.IntermediateLocation
import java.nio.file.Path
import kotlin.io.path.Path
import kotlin.io.path.relativeTo

/**
 * Builds SARIF physical/logical locations for Go IR instructions from
 * [GoIRPosition]. Go positions carry only start line/column, so produced regions
 * have no end coordinates. Missing positions fall back to the instruction's
 * recorded line number (or line 1) and the function's fully-qualified name as URI.
 */
class GoLocationResolver(private val sourceRoot: Path?): SarifLocationResolver<IntermediateLocation> {

    override fun generateSarifLocation(location: IntermediateLocation): Location {
        val position = (location.inst as? GoIRInst)?.location?.position
        return Location(
            physicalLocation = PhysicalLocation(
                artifactLocation = ArtifactLocation(
                    uri = uriFor(position, location),
                    uriBaseID = SarifGenerationOptions.LOCATION_URI,
                ),
                region = regionFor(position, location),
            ),
            logicalLocations = listOf(
                LogicalLocation(
                    fullyQualifiedName = location.info.fullyQualified,
                    decoratedName = location.info.machineName,
                ),
            ),
            message = location.message?.let { Message(text = it.replaceFirstChar(Char::uppercase)) },
        )
    }

    override fun resolve(locations: List<IntermediateLocation>): List<ThreadFlowLocation> =
        locations.mapIndexed { idx, loc ->
            ThreadFlowLocation(
                executionOrder = idx.toLong(),
                kinds = listOf(loc.kind),
                location = generateSarifLocation(loc),
            )
        }

    private fun regionFor(position: GoIRPosition?, location: IntermediateLocation): Region {
        if (position != null && position.line > 0) {
            return Region(
                startLine = position.line.toLong(),
                startColumn = position.column.takeIf { it > 0 }?.toLong(),
            )
        }
        val line = location.info.lineNumber
        return Region(startLine = if (line > 0) line.toLong() else 1L)
    }

    private fun uriFor(position: GoIRPosition?, location: IntermediateLocation): String {
        val filename = position?.filename?.takeIf { it.isNotBlank() }
            ?: return location.info.fullyQualified.ifEmpty { "<unknown>" }
        val path = Path(filename)
        val relative = sourceRoot?.let { root -> runCatching { path.relativeTo(root) }.getOrNull() }
        return (relative ?: path).toString()
    }
}
