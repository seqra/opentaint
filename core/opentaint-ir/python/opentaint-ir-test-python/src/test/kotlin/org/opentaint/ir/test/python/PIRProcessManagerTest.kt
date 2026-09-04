package org.opentaint.ir.test.python

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows
import org.opentaint.ir.impl.python.PIRProcessManager
import org.opentaint.ir.impl.python.PIRServerStartupException
import java.nio.file.Files
import java.nio.file.attribute.PosixFilePermissions
import java.time.Duration

class PIRProcessManagerTest {

    @Test
    fun `startup fails within the timeout when readiness is never reported`() {
        val script = writeScript("#!/bin/sh\nsleep 300\n")
        val manager = PIRProcessManager(
            pythonExecutable = script,
            startupTimeout = Duration.ofSeconds(2),
        )

        val elapsed = measureMillis {
            assertThrows<PIRServerStartupException> { manager.start() }
        }
        manager.close()

        assertTrue(elapsed < 30_000, "start() must honour startupTimeout, took ${elapsed}ms")
        assertFalse(manager.isRunning, "the hung server process must be destroyed")
    }

    @Test
    fun `startup fails when the server dies before reporting readiness`() {
        val script = writeScript("#!/bin/sh\nexit 3\n")
        val manager = PIRProcessManager(
            pythonExecutable = script,
            startupTimeout = Duration.ofSeconds(30),
        )

        val error = assertThrows<PIRServerStartupException> { manager.start() }
        manager.close()

        assertTrue(
            error.message!!.contains("exited with code 3"),
            "expected the exit code in the message, got: ${error.message}",
        )
    }

    private fun writeScript(body: String): String {
        val dir = Files.createTempDirectory("pir-fake-server")
        dir.toFile().deleteOnExit()
        val file = dir.resolve("fake-server")
        Files.writeString(file, body)
        Files.setPosixFilePermissions(file, PosixFilePermissions.fromString("rwxr-xr-x"))
        file.toFile().deleteOnExit()
        return file.toAbsolutePath().toString()
    }

    private fun measureMillis(block: () -> Unit): Long {
        val start = System.nanoTime()
        block()
        return (System.nanoTime() - start) / 1_000_000
    }
}
