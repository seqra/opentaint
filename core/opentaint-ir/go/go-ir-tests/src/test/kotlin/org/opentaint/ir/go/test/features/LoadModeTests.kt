package org.opentaint.ir.go.test.features

import org.assertj.core.api.Assertions.assertThat
import org.assertj.core.api.Assertions.assertThatThrownBy
import org.junit.jupiter.api.Test
import org.opentaint.ir.go.api.GoIRBodyUnavailableException
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.ir.go.client.GoIRLoadMode
import java.nio.file.Files
import java.nio.file.Path

class LoadModeTests {
    private fun writeWorkspace(): Path {
        val root = Files.createTempDirectory("goir-modes")
        val dep = root.resolve("dep")
        Files.createDirectories(dep)
        dep.resolve("go.mod").toFile().writeText("module example.com/dep\ngo 1.22\n")
        dep.resolve("dep.go").toFile().writeText(
            "package dep\nfunc Helper(s string) string { return s + \"!\" }\n",
        )
        root.resolve("go.mod").toFile().writeText(
            "module example.com/app\ngo 1.22\nrequire example.com/dep v0.0.0\nreplace example.com/dep => ./dep\n",
        )
        root.resolve("main.go").toFile().writeText(
            "package main\nimport (\n\t\"strings\"\n\t\"example.com/dep\"\n)\nfunc Run(s string) string { return strings.ToUpper(dep.Helper(s)) }\nfunc main() { println(Run(\"x\")) }\n",
        )
        return root
    }

    @Test
    fun `PROJECT mode loads project bodies but not dependency or stdlib bodies`() {
        val root = writeWorkspace()
        GoIRClient().use { client ->
            val prog = client.buildFromDir(root, GoIRLoadConfig(mode = GoIRLoadMode.PROJECT)).program

            val run = prog.findPackage("example.com/app")!!.functions.first { it.name == "Run" }
            assertThat(run.hasBody).isTrue()
            assertThat(run.bodyAvailable).isTrue()
            assertThat(run.body).isNotNull()

            val helper = prog.findPackage("example.com/dep")!!.functions.first { it.name == "Helper" }
            assertThat(helper.hasBody).isTrue()
            assertThat(helper.bodyAvailable).isFalse()
            assertThatThrownBy { helper.body }.isInstanceOf(GoIRBodyUnavailableException::class.java)

            assertThat(prog.findPackage("example.com/dep")!!.isDependency).isTrue()
            assertThat(prog.findPackage("strings")!!.isStdlib).isTrue()
        }
    }

    @Test
    fun `FULL mode loads dependency and stdlib bodies`() {
        val root = writeWorkspace()
        GoIRClient().use { client ->
            val prog = client.buildFromDir(root, GoIRLoadConfig(mode = GoIRLoadMode.FULL)).program
            val helper = prog.findPackage("example.com/dep")!!.functions.first { it.name == "Helper" }
            assertThat(helper.bodyAvailable).isTrue()
            assertThat(helper.body).isNotNull()
            val strings = prog.findPackage("strings")!!
            assertThat(strings.functions.any { it.bodyAvailable }).isTrue()
        }
    }

    @Test
    fun `projectModules promotes a dependency module to project bodies in PROJECT mode`() {
        val root = writeWorkspace()
        GoIRClient().use { client ->
            val prog = client.buildFromDir(
                root,
                GoIRLoadConfig(mode = GoIRLoadMode.PROJECT, projectModules = setOf("example.com/dep")),
            ).program
            val helper = prog.findPackage("example.com/dep")!!.functions.first { it.name == "Helper" }
            assertThat(helper.bodyAvailable).isTrue()
            assertThat(prog.findPackage("example.com/dep")!!.isDependency).isFalse()
            assertThat(prog.findPackage("strings")!!.functions.any { it.bodyAvailable }).isFalse()
        }
    }
}
