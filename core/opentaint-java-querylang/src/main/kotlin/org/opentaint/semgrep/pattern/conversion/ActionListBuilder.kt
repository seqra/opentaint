package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.SemgrepJavaPattern
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import java.util.Optional
import java.util.concurrent.ConcurrentHashMap
import kotlin.jvm.optionals.getOrNull

interface ActionListBuilder<P : Any> {
    fun createActionList(
        pattern: P,
        semgrepTrace: SemgrepRuleLoadStepTrace,
    ): SemgrepPatternActionList?

    fun cached(): ActionListBuilder<P> = CachedActionListBuilder(this)

    companion object {
        fun createJava(): ActionListBuilder<SemgrepJavaPattern> = PatternToActionListConverter()
    }
}

class CachedActionListBuilder<P : Any>(
    private val builder: ActionListBuilder<P>
) : ActionListBuilder<P> {
    private val cache = ConcurrentHashMap<P, Optional<SemgrepPatternActionList>>()

    override fun createActionList(
        pattern: P,
        semgrepTrace: SemgrepRuleLoadStepTrace,
    ): SemgrepPatternActionList? =
        cache.computeIfAbsent(pattern) {
            Optional.ofNullable(builder.createActionList(pattern, semgrepTrace))
        }.getOrNull()
}
