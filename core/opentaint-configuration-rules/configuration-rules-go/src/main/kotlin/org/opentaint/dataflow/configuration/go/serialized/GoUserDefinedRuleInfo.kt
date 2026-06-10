package org.opentaint.dataflow.configuration.go.serialized

interface GoUserDefinedRuleInfo: ItemInfo {
    val relevantTaintMarks: Set<String>
}
