package org.opentaint.ir.go.test

import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.BuildResult
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import java.nio.file.Path

class GoIRTestBuilder : AutoCloseable {
    private val client = GoIRClient()

    fun buildFromSource(source: String, packageName: String = "p"): GoIRProgram =
        client.buildFromSource(source, packageName)

    fun buildFromDir(dir: Path, config: GoIRLoadConfig = GoIRLoadConfig()): GoIRProgram =
        client.buildFromDir(dir, config).program

    fun buildFromDirWithTimings(dir: Path, config: GoIRLoadConfig = GoIRLoadConfig()): BuildResult =
        client.buildFromDir(dir, config)

    override fun close() = client.close()
}
