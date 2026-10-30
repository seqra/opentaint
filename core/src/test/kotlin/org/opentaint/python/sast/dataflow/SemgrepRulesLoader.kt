package org.opentaint.python.sast.dataflow

import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonRule
import org.opentaint.dataflow.python.rules.PIRConfigTaintRulesProvider
import org.opentaint.dataflow.python.rules.PIRTaintConfiguration
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.python.pattern.conversion.PythonLanguageStrategy
import org.opentaint.semgrep.python.pattern.conversion.toSerializedPythonTaintConfig
import kotlin.io.path.extension
import kotlin.io.path.readText
import kotlin.io.path.relativeTo
import kotlin.io.path.toPath
import kotlin.io.path.walk

fun loadSemgrepRules(resourceDir: String): PIRConfigTaintRulesProvider {
    val rulesRoot = Thread.currentThread().contextClassLoader.getResource(resourceDir.removePrefix("/"))
        ?.toURI()?.toPath()
        ?: error("Missing rule dir $resourceDir")

    val loader = SemgrepRuleLoader(listOf(PythonLanguageStrategy()))
    val trace = SemgrepLoadTrace()
    rulesRoot.walk().filter { it.extension == "yaml" || it.extension == "yml" }.forEach { rulePath ->
        loader.registerRuleSet(rulePath.readText(), rulePath.relativeTo(rulesRoot), rulesRoot, trace)
    }

    val taintConfig = PIRTaintConfiguration()
    loader.loadRules().rulesWithMeta.forEach { rule ->
        @Suppress("UNCHECKED_CAST")
        val typed = rule.first as TaintRuleFromSemgrep<SerializedPythonRule>
        taintConfig.loadConfig(typed.toSerializedPythonTaintConfig())
    }

    return PIRConfigTaintRulesProvider(taintConfig)
}
