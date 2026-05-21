package org.opentaint.semgrep.pattern.conversion

data class SemgrepGoPatternActionList(
    val actions: List<SemgrepGoPatternAction>,
    val hasEllipsisInTheBeginning: Boolean,
    val hasEllipsisInTheEnd: Boolean,
)
