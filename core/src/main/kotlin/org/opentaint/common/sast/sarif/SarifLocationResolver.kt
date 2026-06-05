package org.opentaint.common.sast.sarif

import io.github.detekt.sarif4k.Location
import io.github.detekt.sarif4k.ThreadFlowLocation

interface SarifLocationResolver<IL> {
    fun resolve(locations: List<IL>): List<ThreadFlowLocation>
    fun generateSarifLocation(location: IL): Location
}
