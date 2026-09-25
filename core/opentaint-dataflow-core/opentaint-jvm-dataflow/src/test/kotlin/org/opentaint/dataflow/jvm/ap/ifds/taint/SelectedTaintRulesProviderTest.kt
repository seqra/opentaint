package org.opentaint.dataflow.jvm.ap.ifds.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.taint.ActionableRules
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.Condition
import org.opentaint.dataflow.configuration.jvm.Result as ResultPosition
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMark
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.configuration.jvm.TaintSinkMeta
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.jvm.JIRField
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * Unit tests for [SelectedTaintRulesProvider] (spec §10, gaps G5/G6). Every
 * scenario uses a fake [TaintRulesProvider] delegate that returns a fixed
 * answer per statement, so what is under test is purely the provider's
 * filter semantics.
 */
class SelectedTaintRulesProviderTest {

    private val fakeMethod = object : CommonMethod {
        override val name: String = "fake"
        override val parameters: List<CommonMethodParameter> = emptyList()
        override val returnType: CommonTypeName = object : CommonTypeName {
            override val typeName: String = "void"
        }

        override fun flowGraph() = error("not needed for this test")
    }

    private fun fakeInst(name: String): CommonInst = object : CommonInst {
        override val location: CommonInstLocation get() = error("not needed for this test")
        override fun toString(): String = name
    }

    private val s1 = fakeInst("s1")
    private val s2 = fakeInst("s2")

    @Suppress("UNCHECKED_CAST")
    private val trueCondition = CommonCondition.True as Condition

    private fun mark(name: String) = AssignMark(TaintMark(name), ResultPosition)

    private fun sourceRule(actions: List<AssignMark>) = TaintMethodSource(
        method = fakeMethod,
        condition = trueCondition,
        actionsAfter = actions,
        info = null,
    )

    private fun sinkRule() = TaintMethodSink(
        method = fakeMethod,
        condition = trueCondition,
        trackFactsReachAnalysisEnd = emptyList(),
        id = "sink",
        meta = TaintSinkMeta(message = "m", severity = CommonTaintConfigurationSinkMeta.Severity.Warning, cwe = null),
        info = null,
    )

    private fun exitSinkRule() = TaintMethodExitSink(
        method = fakeMethod,
        condition = trueCondition,
        trackFactsReachAnalysisEnd = emptyList(),
        id = "exit-sink",
        meta = TaintSinkMeta(message = "m", severity = CommonTaintConfigurationSinkMeta.Severity.Warning, cwe = null),
        info = null,
    )

    /** All members no-op/empty unless overridden per test. */
    private open class FixedDelegate(
        private val sources: Map<CommonInst, List<TaintMethodSource>> = emptyMap(),
        private val sinks: Map<CommonInst, List<TaintMethodSink>> = emptyMap(),
        private val exitSinks: Map<CommonInst, List<TaintMethodExitSink>> = emptyMap(),
        private val cleaners: Map<CommonInst, List<TaintCleaner>> = emptyMap(),
        private val passThroughs: List<TaintPassThrough> = emptyList(),
    ) : TaintRulesProvider {
        override fun entryPointRulesForMethod(
            method: CommonMethod,
            statement: CommonInst,
            fact: FactAp?,
            allRelevant: Boolean,
        ): Iterable<TaintEntryPointSource> = emptyList()

        override fun sourceRulesForMethod(
            method: CommonMethod,
            statement: CommonInst,
            fact: FactAp?,
            allRelevant: Boolean,
        ): Iterable<TaintMethodSource> = sources[statement] ?: emptyList()

        override fun exitSourceRulesForMethod(
            method: CommonMethod,
            statement: CommonInst,
            fact: FactAp?,
            allRelevant: Boolean,
        ): Iterable<TaintMethodExitSource> = emptyList()

        override fun sinkRulesForMethod(
            method: CommonMethod,
            statement: CommonInst,
            fact: FactAp?,
            allRelevant: Boolean,
        ): Iterable<TaintMethodSink> = sinks[statement] ?: emptyList()

        override fun sinkRulesForMethodEntry(
            method: CommonMethod,
            statement: CommonInst,
            fact: FactAp?,
            allRelevant: Boolean,
        ): Iterable<TaintMethodEntrySink> = emptyList()

        override fun sinkRulesForMethodExit(
            method: CommonMethod,
            statement: CommonInst,
            fact: FactAp?,
            initialFacts: Set<InitialFactAp>?,
            allRelevant: Boolean,
        ): Iterable<TaintMethodExitSink> = exitSinks[statement] ?: emptyList()

        override fun passTroughRulesForMethod(
            method: CommonMethod,
            statement: CommonInst?,
            fact: FactAp?,
            allRelevant: Boolean,
        ): Iterable<TaintPassThrough> = passThroughs

        override fun cleanerRulesForMethod(
            method: CommonMethod,
            statement: CommonInst,
            fact: FactAp?,
            allRelevant: Boolean,
        ): Iterable<TaintCleaner> = cleaners[statement] ?: emptyList()

        override fun sourceRulesForStaticField(
            field: JIRField,
            statement: CommonInst,
            fact: FactAp?,
            allRelevant: Boolean,
        ): Iterable<TaintStaticFieldSource> = emptyList()

        override fun selectRules(ruleIds: Set<String>) {}
    }

    /**
     * Mirrors `org.opentaint.jvm.sast.dataflow.JIRMethodExitRuleProvider`'s exit-sink gate: apply
     * method exit rules on Z2F edges only. That class lives in a separate Gradle build
     * (opentaint-jvm-sast-dataflow, which depends on this module, not the other way round), so it
     * cannot be imported here without a cycle; this reproduces its exact logic to cover the G5
     * regression (the provider must filter the delegate's answer, not replace it).
     */
    private class ExitRuleGate(private val base: TaintRulesProvider) : TaintRulesProvider by base {
        override fun sinkRulesForMethodExit(
            method: CommonMethod,
            statement: CommonInst,
            fact: FactAp?,
            initialFacts: Set<InitialFactAp>?,
            allRelevant: Boolean,
        ): Iterable<TaintMethodExitSink> {
            if (!initialFacts.isNullOrEmpty()) return emptyList()
            return base.sinkRulesForMethodExit(method, statement, fact, initialFacts, allRelevant)
        }
    }

    private fun fakeInitialFactAp(): InitialFactAp = object : InitialFactAp {
        override val base: AccessPathBase get() = error("not needed for this test")
        override val exclusions: ExclusionSet get() = error("not needed for this test")
        override val size: Int get() = error("not needed for this test")
        override val depth: Int get() = error("not needed for this test")
        override fun startsWithAccessor(accessor: Accessor) = error("not needed for this test")
        override fun getStartAccessors(): Set<Accessor> = error("not needed for this test")
        override fun getAllAccessors(): Set<Accessor> = error("not needed for this test")
        override fun isAbstract() = error("not needed for this test")
        override fun readAccessor(accessor: Accessor): InitialFactAp? = error("not needed for this test")
        override fun rebase(newBase: AccessPathBase) = error("not needed for this test")
        override fun exclude(accessor: Accessor) = error("not needed for this test")
        override fun replaceExclusions(exclusions: ExclusionSet) = error("not needed for this test")
        override fun prependAccessor(accessor: Accessor) = error("not needed for this test")
        override fun clearAccessor(accessor: Accessor): InitialFactAp? = error("not needed for this test")
        override fun splitDelta(other: FinalFactAp): List<Pair<InitialFactAp, InitialFactAp.Delta>> =
            error("not needed for this test")

        override fun concat(delta: InitialFactAp.Delta) = error("not needed for this test")
        override fun contains(factAp: InitialFactAp) = error("not needed for this test")
        override fun compatibilityFilter(typeChecker: FactTypeChecker): FactTypeChecker.FactCompatibilityFilter =
            error("not needed for this test")
    }

    @Test
    fun `a null selection returns the delegate's rules unchanged`() {
        val rule = sourceRule(listOf(mark("A")))
        val delegate = FixedDelegate(sources = mapOf(s1 to listOf(rule)))
        val provider = SelectedTaintRulesProvider(delegate)

        val result = provider.sourceRulesForMethod(fakeMethod, s1, null).toList()

        assertEquals(listOf(rule), result)
    }

    @Test
    fun `a statement outside the covered set returns the delegate's rules unchanged`() {
        val rule = sourceRule(listOf(mark("A")))
        val delegate = FixedDelegate(sources = mapOf(s1 to listOf(rule)))
        val provider = SelectedTaintRulesProvider(delegate)
        val rules: ActionableRules = mapOf(s2 to mapOf(rule as CommonTaintConfigurationItem to setOf(mark("A") as CommonTaintAction)))
        provider.select(rules, coveredStatements = setOf(s2))

        val result = provider.sourceRulesForMethod(fakeMethod, s1, null).toList()

        assertEquals(listOf(rule), result)
    }

    @Test
    fun `a covered statement with the sink selected keeps it`() {
        val rule = sinkRule()
        val delegate = FixedDelegate(sinks = mapOf(s1 to listOf(rule)))
        val provider = SelectedTaintRulesProvider(delegate)
        val rules: ActionableRules = mapOf(s1 to mapOf(rule as CommonTaintConfigurationItem to emptySet()))
        provider.select(rules, coveredStatements = setOf(s1))

        val result = provider.sinkRulesForMethod(fakeMethod, s1, null).toList()

        assertEquals(listOf(rule), result)
    }

    @Test
    fun `a covered statement with the sink absent drops it`() {
        val rule = sinkRule()
        val delegate = FixedDelegate(sinks = mapOf(s1 to listOf(rule)))
        val provider = SelectedTaintRulesProvider(delegate)
        provider.select(emptyMap(), coveredStatements = setOf(s1))

        val result = provider.sinkRulesForMethod(fakeMethod, s1, null).toList()

        assertTrue(result.isEmpty())
    }

    @Test
    fun `a source with one of two selected actions keeps only that action`() {
        val markA = mark("A")
        val markB = mark("B")
        val rule = sourceRule(listOf(markA, markB))
        val delegate = FixedDelegate(sources = mapOf(s1 to listOf(rule)))
        val provider = SelectedTaintRulesProvider(delegate)
        val rules: ActionableRules =
            mapOf(s1 to mapOf(rule as CommonTaintConfigurationItem to setOf(markA as CommonTaintAction)))
        provider.select(rules, coveredStatements = setOf(s1))

        val result = provider.sourceRulesForMethod(fakeMethod, s1, null).toList()

        assertEquals(1, result.size)
        assertEquals(listOf(markA), result.single().actionsAfter)
    }

    @Test
    fun `a source with no selected actions is dropped`() {
        val markA = mark("A")
        val rule = sourceRule(listOf(markA))
        val delegate = FixedDelegate(sources = mapOf(s1 to listOf(rule)))
        val provider = SelectedTaintRulesProvider(delegate)
        val rules: ActionableRules = mapOf(s1 to mapOf(rule as CommonTaintConfigurationItem to emptySet()))
        provider.select(rules, coveredStatements = setOf(s1))

        val result = provider.sourceRulesForMethod(fakeMethod, s1, null).toList()

        assertTrue(result.isEmpty())
    }

    @Test
    fun `an exit sink stays empty on a non-empty initialFacts even when selected`() {
        val rule = exitSinkRule()
        val delegate = FixedDelegate(exitSinks = mapOf(s1 to listOf(rule)))
        val gated = ExitRuleGate(delegate)
        val provider = SelectedTaintRulesProvider(gated)
        val rules: ActionableRules = mapOf(s1 to mapOf(rule as CommonTaintConfigurationItem to emptySet()))
        provider.select(rules, coveredStatements = setOf(s1))

        val result = provider.sinkRulesForMethodExit(
            fakeMethod, s1, null, initialFacts = setOf(fakeInitialFactAp()),
        ).toList()

        assertTrue(result.isEmpty())
    }

    @Test
    fun `allRelevant returns the delegate's rules unchanged even when covered`() {
        val rule = sourceRule(listOf(mark("A")))
        val delegate = FixedDelegate(sources = mapOf(s1 to listOf(rule)))
        val provider = SelectedTaintRulesProvider(delegate)
        provider.select(emptyMap(), coveredStatements = setOf(s1))

        val result = provider.sourceRulesForMethod(fakeMethod, s1, null, allRelevant = true).toList()

        assertEquals(listOf(rule), result)
    }

    @Test
    fun `cleaners always delegate regardless of selection`() {
        val rule = TaintCleaner(fakeMethod, trueCondition, emptyList(), info = null)
        val delegate = FixedDelegate(cleaners = mapOf(s1 to listOf(rule)))
        val provider = SelectedTaintRulesProvider(delegate)
        provider.select(emptyMap(), coveredStatements = setOf(s1))

        val result = provider.cleanerRulesForMethod(fakeMethod, s1, null).toList()

        assertEquals(listOf(rule), result)
    }

    @Test
    fun `pass-throughs always delegate regardless of selection`() {
        val rule = TaintPassThrough(fakeMethod, trueCondition, emptyList(), info = null)
        val delegate = FixedDelegate(passThroughs = listOf(rule))
        val provider = SelectedTaintRulesProvider(delegate)
        provider.select(emptyMap(), coveredStatements = setOf(s1))

        val result = provider.passTroughRulesForMethod(fakeMethod, s1, null).toList()

        assertEquals(listOf(rule), result)
    }
}
