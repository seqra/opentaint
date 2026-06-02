package org.opentaint.dataflow.go.analysis.alias

import org.opentaint.dataflow.ap.ifds.AccessPathBase

object AliasDirective {
    data class Path(val base: AccessPathBase, val accessors: List<GoAliasAccessor>, val negated: Boolean)
    data class Expectation(val paths: List<Path>, val sourceLine: Int)
    data class Parsed(val depth: Int, val expectations: List<Expectation>)

    fun parsePath(raw: String): Path {
        var s = raw.trim()
        val negated = s.startsWith("!")
        if (negated) s = s.substring(1).trim()
        val baseMatch = Regex("^arg(\\d+)").find(s) ?: error("Path must start with argN: $raw")
        val base = AccessPathBase.Argument(baseMatch.groupValues[1].toInt())
        var rest = s.substring(baseMatch.value.length)
        val accessors = mutableListOf<GoAliasAccessor>()
        while (rest.isNotEmpty()) {
            when {
                rest.startsWith("[]") -> { accessors.add(GoAliasAccessor.Array); rest = rest.substring(2) }
                rest.startsWith("@") -> { accessors.add(GoAliasAccessor.Ref); rest = rest.substring(1) }
                rest.startsWith(".") -> {
                    val m = Regex("^\\.([A-Za-z0-9_]+)").find(rest) ?: error("Bad field accessor: $rest")
                    accessors.add(GoAliasAccessor.Field("", m.groupValues[1]))
                    rest = rest.substring(m.value.length)
                }
                else -> error("Bad accessor in path: $raw at $rest")
            }
        }
        return Path(base, accessors, negated)
    }

    fun parseSource(src: String): Parsed {
        val lines = src.lines()
        var depth = 0
        val expectations = mutableListOf<Expectation>()
        for ((i, line) in lines.withIndex()) {
            val t = line.trim()
            if (t.startsWith("// depth:")) {
                depth = t.removePrefix("// depth:").trim().toInt()
            }
            if (t.startsWith("// alias:")) {
                val paths = t.removePrefix("// alias:").split(",").map { it.trim() }.filter { it.isNotEmpty() }.map { parsePath(it) }
                expectations.add(Expectation(paths, i))
            }
        }
        return Parsed(depth, expectations)
    }
}
