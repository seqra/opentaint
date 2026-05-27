package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.PatternParsingAstFailed
import org.opentaint.semgrep.pattern.PatternParsingFailure
import org.opentaint.semgrep.pattern.PatternParsingFailureWithElement
import org.opentaint.semgrep.pattern.SemgrepJavaPattern
import org.opentaint.semgrep.pattern.SemgrepJavaPatternParser
import org.opentaint.semgrep.pattern.SemgrepJavaPatternParsingResult
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import java.util.Optional
import java.util.concurrent.ConcurrentHashMap
import kotlin.jvm.optionals.getOrNull

interface SemgrepPatternParser<P : Any> {
    fun parseOrNull(
        pattern: String,
        semgrepTrace: SemgrepRuleLoadStepTrace,
    ): P?

    fun cached(): SemgrepPatternParser<P> = CachedSemgrepPatternParser(this)

    companion object {
        fun createJava(): SemgrepPatternParser<SemgrepJavaPattern> = DefaultSemgrepPatternParser()
    }
}

class DefaultSemgrepPatternParser(
    private val parser: SemgrepJavaPatternParser = SemgrepJavaPatternParser()
) : SemgrepPatternParser<SemgrepJavaPattern> {
    override fun parseOrNull(
        pattern: String,
        semgrepTrace: SemgrepRuleLoadStepTrace,
    ): SemgrepJavaPattern? {
        return when (val result = parser.parseSemgrepJavaPattern(pattern)) {
            is SemgrepJavaPatternParsingResult.FailedASTParsing -> {
                semgrepTrace.error(PatternParsingAstFailed(result.errorMessages))
                null
            }

            is SemgrepJavaPatternParsingResult.Ok -> {
                result.pattern
            }

            is SemgrepJavaPatternParsingResult.ParserFailure -> {
                semgrepTrace.error(
                    PatternParsingFailureWithElement(
                        result.exception.message,
                        result.exception.element.text,
                    )
                )
                null
            }

            is SemgrepJavaPatternParsingResult.OtherFailure -> {
                semgrepTrace.error(PatternParsingFailure(result.exception.message))
                null
            }
        }
    }
}

class CachedSemgrepPatternParser<P : Any>(
    private val parser: SemgrepPatternParser<P>,
) : SemgrepPatternParser<P> {
    private val cache = ConcurrentHashMap<String, Optional<P>>()

    override fun parseOrNull(
        pattern: String,
        semgrepTrace: SemgrepRuleLoadStepTrace,
    ): P? =
        cache.computeIfAbsent(pattern) {
            Optional.ofNullable(parser.parseOrNull(pattern, semgrepTrace))
        }.getOrNull()
}
