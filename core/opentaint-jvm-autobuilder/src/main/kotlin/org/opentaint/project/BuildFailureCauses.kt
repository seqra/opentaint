package org.opentaint.project

sealed class BuildFailureCauses(private val tool: String) {
    private val causes = mutableListOf<String>()

    abstract fun accept(line: String)

    fun causes(exitCode: Int): List<String> =
        causes.toList().ifEmpty { listOf("the $tool build failed with exit code $exitCode") }

    protected fun addCause(text: String) {
        text.trim().takeIf { it.isNotEmpty() }?.let { causes += it }
    }
}

class GradleFailureCauses : BuildFailureCauses("Gradle") {
    private var inFailureBlock = false

    override fun accept(line: String) {
        val text = line.trim()
        when {
            text == "* What went wrong:" -> inFailureBlock = true
            !inFailureBlock -> {}
            text.startsWith("* ") -> inFailureBlock = false
            else -> addCause(text.removePrefix(">"))
        }
    }
}

class MavenFailureCauses : BuildFailureCauses("Maven") {
    private var inFailureBlock = false

    override fun accept(line: String) {
        if (!line.startsWith(ERROR_PREFIX)) return
        val text = line.removePrefix(ERROR_PREFIX).trim()
        if (text.startsWith("Failed to execute goal")) inFailureBlock = true
        if (!inFailureBlock) return

        // Maven appends the reference to a one-line message and puts it on its own line otherwise.
        val helpReference = HELP_REFERENCE.find(text)
        addCause(helpReference?.let { text.substring(0, it.range.first) } ?: text)
        if (helpReference != null) inFailureBlock = false
    }

    companion object {
        private const val ERROR_PREFIX = "[ERROR]"
        private val HELP_REFERENCE = Regex("""-> \[Help \d+]$""")
    }
}
