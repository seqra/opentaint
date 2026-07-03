package org.opentaint.semgrep.pattern

fun SemgrepFileLoadTrace.errorEntries(): List<SemgrepErrorEntry> =
    entries.filterIsInstance<SemgrepErrorEntry>() +
        ruleTraces.flatMap { rule ->
            rule.entries.filterIsInstance<SemgrepErrorEntry>() +
                rule.steps.flatMap { step -> step.entries.filterIsInstance<SemgrepErrorEntry>() }
        }

fun SemgrepLoadTrace.errorEntries(): List<SemgrepErrorEntry> = fileTraces.flatMap { it.errorEntries() }

fun SemgrepFileLoadTrace.errorMessages(): List<String> = errorEntries().map { it.message }

fun SemgrepLoadTrace.errorMessages(): List<String> = errorEntries().map { it.message }
