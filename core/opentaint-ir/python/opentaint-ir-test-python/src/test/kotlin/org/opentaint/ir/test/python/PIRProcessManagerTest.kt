package org.opentaint.ir.test.python

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRProcessManager
import org.opentaint.ir.impl.python.PIRServerConnection
import org.opentaint.ir.impl.python.PIRServerStartupException
import java.nio.file.Files
import java.nio.file.Paths
import java.nio.file.attribute.PosixFilePermissions
import kotlin.time.Duration.Companion.seconds
import java.util.stream.Collectors

class PIRProcessManagerTest {

    @Test
    fun `startup fails within the timeout when readiness is never reported`() {
        val script = writeScript("#!/bin/sh\nexec sleep 300\n")
        val manager = PIRProcessManager(
            pythonExecutable = script,
            startupTimeout = 2.seconds,
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
            startupTimeout = 30.seconds,
        )

        val error = assertThrows<PIRServerStartupException> { manager.start() }
        manager.close()

        assertTrue(
            error.message!!.contains("exited with code 3"),
            "expected the exit code in the message, got: ${error.message}",
        )
    }

    @Test
    fun `start rejects a second invocation instead of orphaning the first process`() {
        val script = writeScript("#!/bin/sh\nexec sleep 300\n")
        val manager = PIRProcessManager(
            pythonExecutable = script,
            startupTimeout = 2.seconds,
        )

        assertThrows<PIRServerStartupException> { manager.start() }
        assertThrows<IllegalStateException> { manager.start() }
        manager.close()
    }

    @Test
    fun `opening a connection to a server that dies leaves no working directory behind`() {
        val script = writeScript("#!/bin/sh\nexit 3\n")
        val settings = PIRSettings(
            sources = emptyList(),
            packageRoots = listOf("."),
            pythonExecutable = script,
            serverStartupTimeout = 30.seconds,
        )

        val before = serverWorkingDirectories()
        assertThrows<PIRServerStartupException> { PIRServerConnection.open(settings) }

        assertEquals(before, serverWorkingDirectories(), "the server working directory leaked")
    }

    private fun serverWorkingDirectories(): Set<String> {
        val tmp = Paths.get(System.getProperty("java.io.tmpdir"))
        Files.list(tmp).use { paths ->
            return paths
                .map { it.fileName.toString() }
                .filter { it.startsWith("pir-server-cwd") }
                .collect(Collectors.toSet())
        }
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
