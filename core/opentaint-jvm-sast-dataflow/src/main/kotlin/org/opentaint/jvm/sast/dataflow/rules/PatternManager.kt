package org.opentaint.jvm.sast.dataflow.rules

import java.util.concurrent.ConcurrentHashMap

class PatternManager {
    private val compiledMatchers = ConcurrentHashMap<String, Regex>()

    fun compilePattern(pattern: String): Regex =
        compiledMatchers.computeIfAbsent(pattern) { it.toRegex() }

    fun matchPattern(pattern: String, str: String): Boolean =
        compilePattern(pattern).containsMatchIn(str)
}
