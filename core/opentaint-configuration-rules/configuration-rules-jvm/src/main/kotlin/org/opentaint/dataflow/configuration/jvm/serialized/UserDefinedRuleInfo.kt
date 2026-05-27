package org.opentaint.dataflow.configuration.jvm.serialized

interface UserDefinedRuleInfo: ItemInfo {
    val relevantTaintMarks: Set<String>
}
