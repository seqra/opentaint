package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.PassThrough
import org.opentaint.go.config.GoConfigLoader
import kotlin.test.Test

/**
 * Diagnostic-only test class: dumps the engine's per-statement fact set for
 * each engine-roadmap pattern's *001T entry point. Not assertions — output is
 * piped through `--info` and used to ground the "current fact annotations"
 * sections of docs/superpowers/specs/2026-05-28-go-engine-improvements-roadmap-design.md.
 *
 * Bundled go-config is enabled here so config-dependent patterns (1, 2, 3)
 * show whatever propagators are currently in place. For the non-config
 * patterns the extra rules are unused.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class EngineRoadmapDiagnosticTest : AnalysisTest() {

    override val commonPassRules: List<PassThrough> =
        GoConfigLoader.getConfig()?.passThrough ?: emptyList()

    // Pattern 1: strings.Builder
    @Test fun diag_p01_stringsBuilderWrite001T() = printFactsAt("test.stringsBuilderWrite001T")

    // Pattern 2: container/list
    @Test fun diag_p02_containerListPushFront001T() = printFactsAt("test.containerListPushFront001T")

    // Pattern 3: sync/atomic.Value
    @Test fun diag_p03_atomicValueLoad001T() = printFactsAt("test.atomicValueLoad001T")

    // Pattern 4: type-assert on chained expression
    @Test fun diag_p04_typeAssertOnMapElem001T() = printFactsAt("test.typeAssertOnMapElem001T")
    @Test fun diag_p04_typeAssertOnFieldRead001T() = printFactsAt("test.typeAssertOnFieldRead001T")
    @Test fun diag_p04_typeAssertOnCallResult001T() = printFactsAt("test.typeAssertOnCallResult001T")

    // Pattern 5: type-switch case binding
    @Test fun diag_p05_typeSwitchBinding001T() = printFactsAt("test.typeSwitchBinding001T")

    // Pattern 6: deep NAMED-field chain (4 levels)
    @Test fun diag_p06_nestedNamedDeep001T() = printFactsAt("test.nestedNamedDeep001T")

    // Pattern 8: new(T) pointer chain
    @Test fun diag_p08_ptrNewWriteAliasRead001T() = printFactsAt("test.ptrNewWriteAliasRead001T")

    // Cluster C: closure capture / higher-order
    @Test fun diag_cC_closureCaptureReturn001T() = printFactsAt("test.closureCaptureReturn001T")

    // Map range iteration (FN: taint lost through for-range)
    @Test fun diag_mapIter001T() = printFactsAt("test.mapIter001T")
    @Test fun diag_mapKeyTaint001T() = printFactsAt("test.mapKeyTaint001T")
}
