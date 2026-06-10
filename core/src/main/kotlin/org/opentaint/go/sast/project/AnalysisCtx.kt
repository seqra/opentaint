package org.opentaint.go.sast.project

import mu.KLogging
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.ir.go.client.GoIRLoadMode
import org.opentaint.project.GoProject

class AnalysisCtx(
    private val prj: GoProject,
    val client: GoIRClient,
) : AutoCloseable by client {
    val cp: GoIRProgram by lazy {
        logger.info { "Building Go IR for project: ${prj.projectDir}" }
        client.buildFromDir(prj.projectDir, GoIRLoadConfig(mode = GoIRLoadMode.PROJECT)).program
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}