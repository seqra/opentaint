package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.SemgrepGoPattern

class PatternToActionListConverter {
    val failedTransformations = mutableMapOf<String, Int>()

    private var nextArtificialId = 0
    private fun provideArtificialMetavar(): MetavarAtom =
        MetavarAtom.createArtificial("${nextArtificialId++}")

    private class TransformationFailed(override val message: String) : Exception(message)
    private fun transformationFailed(reason: String): Nothing = throw TransformationFailed(reason)

    fun createActionList(pattern: SemgrepGoPattern): SemgrepGoPatternActionList? = try {
        transformPatternToActionList(pattern, isRoot = true)
    } catch (ex: TransformationFailed) {
        val reason = ex.message
        failedTransformations[reason] = (failedTransformations[reason] ?: 0) + 1
        null
    }

    private fun transformPatternToActionList(
        pattern: SemgrepGoPattern,
        isRoot: Boolean = false,
    ): SemgrepGoPatternActionList = when (pattern) {
        // Cases added in later tasks.
        else -> {
            val prefix = if (isRoot) "Root pattern is: " else ""
            transformationFailed("$prefix${pattern::class.simpleName}")
        }
    }
}
