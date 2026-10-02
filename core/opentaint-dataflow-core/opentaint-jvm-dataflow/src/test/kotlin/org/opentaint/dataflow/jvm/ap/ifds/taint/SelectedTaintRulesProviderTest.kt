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
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
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
import java.lang.reflect.Proxy
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertSame
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

    @Test
    fun `a restricted source is built once and returned on every query`() {
        val markA = mark("A")
        val rule = sourceRule(listOf(markA, mark("B")))
        val provider = SelectedTaintRulesProvider(FixedDelegate(sources = mapOf(s1 to listOf(rule))))
        provider.select(mapOf(s1 to mapOf(rule to setOf(markA))), coveredStatements = setOf(s1))

        val first = provider.sourceRulesForMethod(fakeMethod, s1, null).single()
        val second = provider.sourceRulesForMethod(fakeMethod, s1, null).single()

        assertEquals(listOf(markA), first.actionsAfter)
        assertSame(first, second)
    }

    @Test
    fun `a source with every action selected is returned as the delegate's instance`() {
        val markA = mark("A")
        val rule = sourceRule(listOf(markA))
        val provider = SelectedTaintRulesProvider(FixedDelegate(sources = mapOf(s1 to listOf(rule))))
        provider.select(mapOf(s1 to mapOf(rule to setOf(markA))), coveredStatements = setOf(s1))

        assertSame(rule, provider.sourceRulesForMethod(fakeMethod, s1, null).single())
    }

    @Test
    fun `a fresh equal copy from the delegate gets the one restricted instance`() {
        // Like the Spring entry-point rules: the delegate builds a new, equal rule on every call.
        val markA = mark("A")
        val selected = sourceRule(listOf(markA, mark("B")))
        val delegate = object : FixedDelegate() {
            override fun sourceRulesForMethod(
                method: CommonMethod,
                statement: CommonInst,
                fact: FactAp?,
                allRelevant: Boolean,
            ): Iterable<TaintMethodSource> = listOf(selected.copy())
        }
        val provider = SelectedTaintRulesProvider(delegate)
        provider.select(mapOf(s1 to mapOf(selected to setOf(markA))), coveredStatements = setOf(s1))

        val first = provider.sourceRulesForMethod(fakeMethod, s1, null).single()
        val second = provider.sourceRulesForMethod(fakeMethod, s1, null).single()

        assertEquals(listOf(markA), first.actionsAfter)
        assertSame(first, second)
    }

    /** The arguments the delegate got, compared by identity. */
    private class Query(
        val method: CommonMethod,
        val statement: CommonInst,
        val fact: FactAp?,
        val initialFacts: Set<InitialFactAp>?,
        val allRelevant: Boolean,
    )

    /**
     * One restricted query: [rules] are the two rules its delegate returns, the first selected with
     * action `A` (a source keeps only `A`) and the second not selected; [ask] runs the query.
     */
    private class RestrictedQuery(
        val name: String,
        val rules: List<CommonTaintConfigurationItem>,
        val ask: TaintRulesProvider.(CommonMethod, CommonInst, FactAp?, Set<InitialFactAp>?) -> Iterable<CommonTaintConfigurationItem>,
    )

    private val selectedMark = mark("A")

    private fun restrictedQueries(): List<RestrictedQuery> {
        val actions = listOf(selectedMark, mark("B"))
        val meta = TaintSinkMeta(message = "m", severity = CommonTaintConfigurationSinkMeta.Severity.Warning, cwe = null)
        fun sinkId(i: Int) = "sink-$i"
        return listOf(
            RestrictedQuery("entryPointRulesForMethod", List(2) { TaintEntryPointSource(fakeMethod, trueCondition, actions, null, "ep-$it") }) { m, s, f, _ ->
                entryPointRulesForMethod(m, s, f, allRelevant = false)
            },
            RestrictedQuery("sourceRulesForMethod", List(2) { TaintMethodSource(fakeMethod, trueCondition, actions, null, "src-$it") }) { m, s, f, _ ->
                sourceRulesForMethod(m, s, f, allRelevant = false)
            },
            RestrictedQuery("exitSourceRulesForMethod", List(2) { TaintMethodExitSource(fakeMethod, trueCondition, actions, null, "exit-src-$it") }) { m, s, f, _ ->
                exitSourceRulesForMethod(m, s, f, allRelevant = false)
            },
            RestrictedQuery("sinkRulesForMethod", List(2) { TaintMethodSink(fakeMethod, trueCondition, emptyList(), sinkId(it), meta, null) }) { m, s, f, _ ->
                sinkRulesForMethod(m, s, f, allRelevant = false)
            },
            RestrictedQuery("sinkRulesForMethodEntry", List(2) { TaintMethodEntrySink(fakeMethod, trueCondition, emptyList(), sinkId(it), meta, null) }) { m, s, f, _ ->
                sinkRulesForMethodEntry(m, s, f, allRelevant = false)
            },
            RestrictedQuery("sinkRulesForMethodExit", List(2) { TaintMethodExitSink(fakeMethod, trueCondition, emptyList(), sinkId(it), meta, null) }) { m, s, f, i ->
                sinkRulesForMethodExit(m, s, f, i, allRelevant = false)
            },
        )
    }

    /** Answers every restricted query with [rules] and records the arguments of each call. */
    private class RecordingDelegate(private val rules: List<CommonTaintConfigurationItem>) : FixedDelegate() {
        val queries = mutableListOf<Query>()

        @Suppress("UNCHECKED_CAST")
        private fun <T> answer(query: Query): Iterable<T> {
            queries += query
            return rules as List<T>
        }

        override fun entryPointRulesForMethod(method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
            answer<TaintEntryPointSource>(Query(method, statement, fact, null, allRelevant))

        override fun sourceRulesForMethod(method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
            answer<TaintMethodSource>(Query(method, statement, fact, null, allRelevant))

        override fun exitSourceRulesForMethod(method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
            answer<TaintMethodExitSource>(Query(method, statement, fact, null, allRelevant))

        override fun sinkRulesForMethod(method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
            answer<TaintMethodSink>(Query(method, statement, fact, null, allRelevant))

        override fun sinkRulesForMethodEntry(method: CommonMethod, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
            answer<TaintMethodEntrySink>(Query(method, statement, fact, null, allRelevant))

        override fun sinkRulesForMethodExit(
            method: CommonMethod,
            statement: CommonInst,
            fact: FactAp?,
            initialFacts: Set<InitialFactAp>?,
            allRelevant: Boolean,
        ) = answer<TaintMethodExitSink>(Query(method, statement, fact, initialFacts, allRelevant))
    }

    @Test
    fun `every restricted query forwards its arguments and filters the delegate's answer`() {
        val fact = Proxy.newProxyInstance(FactAp::class.java.classLoader, arrayOf(FactAp::class.java)) { _, _, _ ->
            error("not needed for this test")
        } as FactAp
        val initialFacts = setOf(fakeInitialFactAp())

        for (query in restrictedQueries()) {
            val delegate = RecordingDelegate(query.rules)
            val provider = SelectedTaintRulesProvider(delegate)
            val (selected, unselected) = query.rules
            val acts: Set<CommonTaintAction> = if (selected is TaintConfigurationSource) setOf(selectedMark) else emptySet()
            provider.select(mapOf(s1 to mapOf(selected to acts)), coveredStatements = setOf(s1))

            val result = query.ask(provider, fakeMethod, s1, fact, initialFacts).toList()

            val forwarded = delegate.queries.single()
            assertSame(fakeMethod, forwarded.method, query.name)
            assertSame(s1, forwarded.statement, query.name)
            assertSame(fact, forwarded.fact, query.name)
            if (query.name == "sinkRulesForMethodExit") assertSame(initialFacts, forwarded.initialFacts, query.name)
            assertFalse(forwarded.allRelevant, query.name)

            val kept = result.single()
            assertTrue(kept !== unselected && kept.javaClass == selected.javaClass, query.name)
            if (kept is TaintConfigurationSource) {
                assertEquals(listOf(selectedMark), kept.actionsAfter, query.name)
                assertEquals((selected as TaintConfigurationSource).serializedId, kept.serializedId, query.name)
            } else {
                assertSame(selected, kept, query.name)
            }
        }
    }
}
