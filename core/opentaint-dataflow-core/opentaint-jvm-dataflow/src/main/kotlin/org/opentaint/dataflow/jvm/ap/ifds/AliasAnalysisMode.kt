package org.opentaint.dataflow.jvm.ap.ifds

/**
 * The backend of [JIRLocalAliasAnalysis].
 *
 * - [DSU]: the DSU alias analysis of main. This is the default.
 * - [SHADOW]: both backends run. The consumers get the DSU answers. The statistics compare the two
 *   answers of each query (`AliasShadowStats`).
 * - [DIRECTED]: the consumers get the answers of the directed alias analysis.
 */
enum class AliasAnalysisMode {
    DSU, SHADOW, DIRECTED;

    companion object {
        /** The system property that sets the mode of the analysis tests. */
        const val TEST_PROPERTY = "opentaint.test.aliasAnalysisMode"

        /** Gets the mode from its name. The case of the name is not important. An unknown name is an error. */
        fun parse(name: String): AliasAnalysisMode =
            entries.firstOrNull { it.name.equals(name.trim(), ignoreCase = true) }
                ?: throw IllegalArgumentException(
                    "Unknown alias analysis mode: '$name'. Use one of ${entries.joinToString { it.name }}"
                )

        /** Gets the mode from [TEST_PROPERTY]. If the property is not set, the mode is [DSU]. */
        fun fromTestProperty(): AliasAnalysisMode =
            System.getProperty(TEST_PROPERTY)?.let(::parse) ?: DSU
    }
}
