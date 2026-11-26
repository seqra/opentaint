package org.opentaint.semgrep.pattern

import java.io.File

object SemgrepRuleUtils {
    fun getRuleId(ruleSetName: String, id: String): String {
        return "$ruleSetName$SEPARATOR$id"
    }

    fun extractRuleSetNameAndId(ruleId: String): Pair<String, String>? {
        val separatorPos = ruleId.indexOf(SEPARATOR)
        if (separatorPos == -1) return null

        val ruleSetName = ruleId.substring(0, separatorPos)
        val rawRuleId = ruleId.substring(separatorPos + 1)
        return ruleSetName to rawRuleId
    }

    fun getSemgrepStyleRuleId(ruleId: String): String {
        val (rulePath, rawRuleId) = extractRuleSetNameAndId(ruleId)
            ?: return ruleId

        val idParts = rulePath.split(File.separatorChar)
            .dropLast(1) + listOf(rawRuleId)

        return idParts.joinToString(separator = ".") { it.trim() }
    }

    private const val SEPARATOR = ':'
}
