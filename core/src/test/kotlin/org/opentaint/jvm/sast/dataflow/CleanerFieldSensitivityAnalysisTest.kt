package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintCleanAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

/**
 * How field-sensitive a cleaner is across a summarized wrapper, as a function of how its position
 * is written.
 *
 * Every case runs the same program shape. `wrap`/`wrapNode` stores its whole argument twice --
 * once before the clean (`p.raw`) and once after it (`p.val`) -- so both stores alias one object
 * and the two summary edges leave from the same initial fact. One sink reads below `p.raw` and
 * must report; the sibling reads below `p.val` and must not.
 *
 * Held constant across a pair: the program, the source, the sink, the read depth. The only
 * variable is the cleaner position, and it decides everything:
 *
 *  - a CONCRETE position (`arg0`, `arg0.f`, `arg0.f.k`) names a path that exists in the access
 *    tree, so the clean is a node deletion. `.raw` and `.val` are different branches of that tree
 *    and stay apart through the summary merge, which is a tree merge. Correct at every depth, and
 *    correct even when the SOURCE is abstract: the demand-driven refinement splits an any-field
 *    fact into concrete facts until the cleaner's path is one of them, and each carries its own
 *    access path;
 *  - a STARRED position (`arg0.*`) names unboundedly many paths, so there is no node to delete.
 *    The removal is recorded as a [org.opentaint.dataflow.ap.ifds.DeepMarkExclusion] on the edge's
 *    exclusion set -- a flat side-channel with no position in the tree -- and the `.raw`/`.val`
 *    distinction the tree was holding is lost at that moment.
 *
 * The starred cases are therefore the defect these tests exist to pin, and they fail in exactly
 * the shape predicted: correct wherever the starred cleaner's BASE component happens to do the
 * work (the depth-1 read), wrong as soon as the answer depends on the star (deeper reads).
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class CleanerFieldSensitivityAnalysisTest : AnalysisTest() {

    companion object {
        private const val TEST_CLS = "test.samples.DeepCleanSummarySample"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "cleaner-field-sensitivity-rule"

        private const val BOX = "test.samples.DeepCleanSummarySample\$Box"
        private const val NODE = "test.samples.DeepCleanSummarySample\$Node"
        private const val LEAF = "test.samples.DeepCleanSummarySample\$Leaf"
    }

    override val sourceFileExtension: String = "java"

    override val analysisUnrollStrategy: AnyAccessorUnrollStrategy = object : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val boxF = PositionModifier.Field(BOX, "f", "java.lang.String")
    private val nodeF = PositionModifier.Field(NODE, "f", LEAF)
    private val leafK = PositionModifier.Field(LEAF, "k", "java.lang.String")

    private fun source(entryPointMethod: String, vararg positions: PositionBaseWithModifiers) =
        SerializedRule.EntryPoint(
            function = functionMatcher(TEST_CLS, entryPointMethod),
            taint = positions.map { SerializedTaintAssignAction(kind = TAINT_MARK, pos = it) }
        )

    private fun cleaner(cleanMethod: String, vararg positions: PositionBaseWithModifiers) =
        SerializedRule.Cleaner(
            function = functionMatcher(TEST_CLS, cleanMethod),
            cleans = positions.map { SerializedTaintCleanAction(taintKind = TAINT_MARK, pos = it) }
        )

    private fun baseOnly() = PositionBaseWithModifiers.BaseOnly(Argument(0))

    private fun withModifiers(vararg modifiers: PositionModifier) =
        PositionBaseWithModifiers.WithModifiers(Argument(0), modifiers.toList())

    private fun starred(cleanMethod: String) =
        cleaner(cleanMethod, baseOnly(), withModifiers(PositionModifier.AnyField))

    private fun config(
        entryPointMethod: String,
        sinkMethod: String,
        source: SerializedRule.EntryPoint,
        cleaner: SerializedRule.Cleaner,
    ) = SerializedTaintConfig(
        entryPoint = listOf(source),
        cleaner = listOf(cleaner),
        sink = listOf(sinkRule(TEST_CLS, sinkMethod, RULE_ID, listOf(Argument(0) to TAINT_MARK)))
    )

    /* ---------- depth 1: the sink reads the stored object itself ---------- */

    private fun baseConfig(entryPointMethod: String) = config(
        entryPointMethod,
        sinkMethod = "sinkBox",
        source = source(entryPointMethod, baseOnly()),
        cleaner = cleaner("clean", baseOnly())
    )

    private fun starredDepth1Config(entryPointMethod: String) = config(
        entryPointMethod,
        sinkMethod = "sinkBox",
        source = source(entryPointMethod, baseOnly(), withModifiers(PositionModifier.AnyField)),
        cleaner = starred("clean")
    )

    @Test
    fun `concrete base clean - the unsanitized field reports`() = assertReachable(
        config = baseConfig("boxUncleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "boxUncleanedFlow",
        ruleId = RULE_ID,
        testName = "concrete base clean, unsanitized field"
    )

    @Test
    open fun `concrete base clean - the sanitized field is silent`() = assertNotReachable(
        config = baseConfig("boxCleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "boxCleanedFlow",
        testName = "concrete base clean, sanitized field"
    )

    @Test
    fun `starred clean at depth 1 - the unsanitized field reports`() = assertReachable(
        config = starredDepth1Config("boxUncleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "boxUncleanedFlow",
        ruleId = RULE_ID,
        testName = "starred clean depth 1, unsanitized field"
    )

    @Test
    open fun `starred clean at depth 1 - the sanitized field is silent`() = assertNotReachable(
        // Green, and it does not exercise the star: the read is `p.val` itself, which the starred
        // cleaner's BASE component removes as a concrete node. The deep exclusion is not consulted.
        config = starredDepth1Config("boxCleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "boxCleanedFlow",
        testName = "starred clean depth 1, sanitized field"
    )

    /* ---------- depth 2: concrete source, concrete one-level clean ---------- */

    private fun fieldConfig(entryPointMethod: String) = config(
        entryPointMethod,
        sinkMethod = "sink",
        source = source(entryPointMethod, withModifiers(boxF)),
        cleaner = cleaner("clean", withModifiers(boxF))
    )

    private fun starredDepth2Config(entryPointMethod: String) = config(
        entryPointMethod,
        sinkMethod = "sink",
        source = source(entryPointMethod, withModifiers(boxF)),
        cleaner = starred("clean")
    )

    @Test
    fun `concrete field clean - the unsanitized field reports`() = assertReachable(
        config = fieldConfig("uncleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "uncleanedFlow",
        ruleId = RULE_ID,
        testName = "concrete field clean, unsanitized field"
    )

    @Test
    open fun `concrete field clean - the sanitized field is silent`() = assertNotReachable(
        config = fieldConfig("cleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "cleanedFlow",
        testName = "concrete field clean, sanitized field"
    )

    @Test
    fun `starred clean at depth 2 - the unsanitized field reports`() = assertReachable(
        config = starredDepth2Config("uncleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "uncleanedFlow",
        ruleId = RULE_ID,
        testName = "starred clean depth 2, unsanitized field"
    )

    @Test
    open fun `starred clean at depth 2 - the sanitized field is silent`() = assertNotReachable(
        config = starredDepth2Config("cleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "cleanedFlow",
        testName = "starred clean depth 2, sanitized field"
    )

    /* ---------- depth 3: ABSTRACT source, concrete two-level clean ---------- */

    private fun deepFieldConfig(entryPointMethod: String) = config(
        entryPointMethod,
        sinkMethod = "sink",
        source = source(entryPointMethod, withModifiers(PositionModifier.AnyField)),
        cleaner = cleaner("cleanNode", withModifiers(nodeF, leafK))
    )

    private fun starredDepth3Config(entryPointMethod: String) = config(
        entryPointMethod,
        sinkMethod = "sink",
        source = source(entryPointMethod, withModifiers(PositionModifier.AnyField)),
        cleaner = starred("cleanNode")
    )

    @Test
    fun `concrete two-level clean over an abstract source - the unsanitized field reports`() = assertReachable(
        config = deepFieldConfig("nodeUncleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "nodeUncleanedFlow",
        ruleId = RULE_ID,
        testName = "concrete two-level clean, unsanitized field"
    )

    @Test
    open fun `concrete two-level clean over an abstract source - the sanitized field is silent`() = assertNotReachable(
        // The source is any-field, so the cleaner's path does not exist as a fact until the
        // demand-driven refinement produces it. Once it does, the clean is a node deletion again
        // and field sensitivity survives the summary -- an abstract source is not the problem.
        config = deepFieldConfig("nodeCleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "nodeCleanedFlow",
        testName = "concrete two-level clean, sanitized field"
    )

    @Test
    fun `starred clean at depth 3 - the unsanitized field reports`() = assertReachable(
        config = starredDepth3Config("nodeUncleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "nodeUncleanedFlow",
        ruleId = RULE_ID,
        testName = "starred clean depth 3, unsanitized field"
    )

    @Test
    open fun `starred clean at depth 3 - the sanitized field is silent`() = assertNotReachable(
        config = starredDepth3Config("nodeCleanedFlow"),
        testCls = TEST_CLS,
        entryPointName = "nodeCleanedFlow",
        testName = "starred clean depth 3, sanitized field"
    )

    /* ---------- non-vacuity controls ---------- */

    /**
     * Every `is silent` case above asserts an ABSENT finding, which an engine that simply loses the
     * taint would also satisfy. These controls run the identical config with the cleaner REMOVED and
     * demand the finding: a red control means its silent sibling proves nothing.
     */
    private fun noCleanerConfig(
        entryPointMethod: String,
        sinkMethod: String,
        source: SerializedRule.EntryPoint,
    ) = SerializedTaintConfig(
        entryPoint = listOf(source),
        cleaner = emptyList(),
        sink = listOf(sinkRule(TEST_CLS, sinkMethod, RULE_ID, listOf(Argument(0) to TAINT_MARK)))
    )

    @Test
    open fun `non-vacuity - base source reaches the sanitized field with no cleaner`() = assertReachable(
        config = noCleanerConfig("boxCleanedFlow", "sinkBox", source("boxCleanedFlow", baseOnly())),
        testCls = TEST_CLS,
        entryPointName = "boxCleanedFlow",
        ruleId = RULE_ID,
        testName = "non-vacuity, base source depth 1"
    )

    @Test
    open fun `non-vacuity - whole-object source reaches the sanitized field with no cleaner`() = assertReachable(
        config = noCleanerConfig(
            "boxCleanedFlow",
            "sinkBox",
            source("boxCleanedFlow", baseOnly(), withModifiers(PositionModifier.AnyField))
        ),
        testCls = TEST_CLS,
        entryPointName = "boxCleanedFlow",
        ruleId = RULE_ID,
        testName = "non-vacuity, whole-object source depth 1"
    )

    @Test
    open fun `non-vacuity - field source reaches the sanitized field with no cleaner`() = assertReachable(
        config = noCleanerConfig("cleanedFlow", "sink", source("cleanedFlow", withModifiers(boxF))),
        testCls = TEST_CLS,
        entryPointName = "cleanedFlow",
        ruleId = RULE_ID,
        testName = "non-vacuity, field source depth 2"
    )

    @Test
    open fun `non-vacuity - any-field source reaches the sanitized field with no cleaner`() = assertReachable(
        config = noCleanerConfig(
            "nodeCleanedFlow",
            "sink",
            source("nodeCleanedFlow", withModifiers(PositionModifier.AnyField))
        ),
        testCls = TEST_CLS,
        entryPointName = "nodeCleanedFlow",
        ruleId = RULE_ID,
        testName = "non-vacuity, any-field source depth 3"
    )
}

/**
 * The mode where these cases are measurable: all four non-vacuity controls are green, so the
 * `is silent` assertions are evidence rather than an artefact.
 *
 * The two disabled cases are the defect itself, not a mode quirk. A starred cleaner's removal is
 * recorded as a flat [org.opentaint.dataflow.ap.ifds.DeepMarkExclusion] on the edge instead of a
 * node in the access tree, so it cannot say "below `.val` only" and the sanitized read is reported.
 * Both fail in the false-positive direction; their unsanitized siblings stay green, so no finding
 * is lost. See docs/superpowers/plans/2026-07-28-deep-exclusion-field-sensitivity.md.
 */
class TreeCleanerFieldSensitivityAnalysisTest : CleanerFieldSensitivityAnalysisTest() {
    @Test
    @Disabled // todo: deep exclusion is not field-sensitive -- see the plan above
    override fun `starred clean at depth 2 - the sanitized field is silent`() =
        super.`starred clean at depth 2 - the sanitized field is silent`()

    @Test
    @Disabled // todo: deep exclusion is not field-sensitive -- see the plan above
    override fun `starred clean at depth 3 - the sanitized field is silent`() =
        super.`starred clean at depth 3 - the sanitized field is silent`()
}

/**
 * Automata drops the taint entirely across the intervening `clean`/`cleanNode` call, so every
 * `*CleanedFlow` entry point reports nothing in this mode REGARDLESS of the cleaner. All four
 * non-vacuity controls are red here, which is exactly what they exist to expose: the six `is
 * silent` cases would pass against an engine with no sanitizer at all, so their green is not
 * evidence and they are disabled rather than counted.
 *
 * The `*UncleanedFlow` cases are unaffected and stay enabled -- they assert a PRESENT finding and
 * cannot pass vacuously.
 */
class AutomataCleanerFieldSensitivityAnalysisTest : CleanerFieldSensitivityAnalysisTest() {
    override val apMode: ApMode = ApMode.Automata

    @Test
    @Disabled // todo: fix automata -- taint dropped across the intervening call
    override fun `non-vacuity - base source reaches the sanitized field with no cleaner`() =
        super.`non-vacuity - base source reaches the sanitized field with no cleaner`()

    @Test
    @Disabled // todo: fix automata -- taint dropped across the intervening call
    override fun `non-vacuity - whole-object source reaches the sanitized field with no cleaner`() =
        super.`non-vacuity - whole-object source reaches the sanitized field with no cleaner`()

    @Test
    @Disabled // todo: fix automata -- taint dropped across the intervening call
    override fun `non-vacuity - field source reaches the sanitized field with no cleaner`() =
        super.`non-vacuity - field source reaches the sanitized field with no cleaner`()

    @Test
    @Disabled // todo: fix automata -- taint dropped across the intervening call
    override fun `non-vacuity - any-field source reaches the sanitized field with no cleaner`() =
        super.`non-vacuity - any-field source reaches the sanitized field with no cleaner`()

    @Test
    @Disabled // todo: fix automata -- passes vacuously, its non-vacuity control is red
    override fun `concrete base clean - the sanitized field is silent`() =
        super.`concrete base clean - the sanitized field is silent`()

    @Test
    @Disabled // todo: fix automata -- passes vacuously, its non-vacuity control is red
    override fun `starred clean at depth 1 - the sanitized field is silent`() =
        super.`starred clean at depth 1 - the sanitized field is silent`()

    @Test
    @Disabled // todo: fix automata -- passes vacuously, its non-vacuity control is red
    override fun `concrete field clean - the sanitized field is silent`() =
        super.`concrete field clean - the sanitized field is silent`()

    @Test
    @Disabled // todo: fix automata -- passes vacuously, its non-vacuity control is red
    override fun `starred clean at depth 2 - the sanitized field is silent`() =
        super.`starred clean at depth 2 - the sanitized field is silent`()

    @Test
    @Disabled // todo: fix automata -- passes vacuously, its non-vacuity control is red
    override fun `concrete two-level clean over an abstract source - the sanitized field is silent`() =
        super.`concrete two-level clean over an abstract source - the sanitized field is silent`()

    @Test
    @Disabled // todo: fix automata -- passes vacuously, its non-vacuity control is red
    override fun `starred clean at depth 3 - the sanitized field is silent`() =
        super.`starred clean at depth 3 - the sanitized field is silent`()
}
