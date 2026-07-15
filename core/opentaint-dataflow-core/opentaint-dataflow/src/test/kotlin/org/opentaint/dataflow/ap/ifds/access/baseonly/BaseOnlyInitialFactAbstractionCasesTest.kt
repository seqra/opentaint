package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class BaseOnlyInitialFactAbstractionCasesTest {
    private val arg0 = AccessPathBase.Argument(0)
    private val field = FieldAccessor("A", "f", "B")
    private val mark = TaintMarkAccessor("m")

    private fun mgr(fieldSensitive: Boolean = false) =
        BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, fieldSensitive = fieldSensitive)

    private fun BaseOnlyApManager.finalOf(vararg accessors: Accessor): FinalFactAp {
        var f = createFinalAp(arg0, ExclusionSet.Empty)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return f
    }

    private fun BaseOnlyApManager.analyzedExcluding(vararg excluded: Accessor): InitialFactAp {
        var f = mostAbstractInitialAp(arg0)
        excluded.forEach { f = f.exclude(it) }
        return f
    }

    private fun BaseOnlyApManager.acc(vararg accessors: Accessor, abstract: Boolean): BaseOnlyAccess =
        BaseOnlyAccessOps.build(IntArray(accessors.size) { interner.index(accessors[it]) }, abstract)

    private fun contains(
        produced: List<Pair<InitialFactAp, FinalFactAp>>,
        initialAccess: BaseOnlyAccess,
        finalAccess: BaseOnlyAccess,
    ): Boolean = produced.any { (initial, final) ->
        initial as BaseOnlyInitialFactAp
        final as BaseOnlyFinalFactAp
        initial.base == arg0 && initial.access == initialAccess && final.access == finalAccess
    }

    @Test
    fun `case A emits any-star always and any-mark when mark excluded`() {
        val m = mgr(false)
        val abstraction = BaseOnlyInitialFactAbstraction(m)
        abstraction.registerNewInitialFact(m.analyzedExcluding(mark), FactTypeChecker.Dummy)

        val produced = abstraction.addAbstractedInitialFact(m.finalOf(AnyAccessor, mark), FactTypeChecker.Dummy)

        assertTrue(contains(produced, m.acc(abstract = true), m.acc(abstract = true)))
        assertTrue(
            contains(
                produced,
                m.acc(mark, FinalAccessor, abstract = false),
                m.acc(mark, abstract = false),
            )
        )
    }

    @Test
    fun `case A emits only any-star when mark not excluded`() {
        val m = mgr(false)
        val abstraction = BaseOnlyInitialFactAbstraction(m)

        val produced = abstraction.addAbstractedInitialFact(m.finalOf(AnyAccessor, mark), FactTypeChecker.Dummy)

        assertTrue(contains(produced, m.acc(abstract = true), m.acc(abstract = true)))
        assertFalse(
            contains(
                produced,
                m.acc(mark, FinalAccessor, abstract = false),
                m.acc(mark, abstract = false),
            )
        )
    }

    @Test
    fun `case B emits base-star then field-any layers gated by exclusions`() {
        val m = mgr(true)
        val abstraction = BaseOnlyInitialFactAbstraction(m)
        abstraction.registerNewInitialFact(m.analyzedExcluding(field, mark), FactTypeChecker.Dummy)

        val produced = abstraction.addAbstractedInitialFact(m.finalOf(field, AnyAccessor, mark), FactTypeChecker.Dummy)

        val fieldAp = BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1)
        assertTrue(contains(produced, fieldAp, fieldAp))
        assertTrue(
            contains(produced, m.acc(field, abstract = true), m.acc(field, abstract = true))
        )
        assertTrue(
            contains(
                produced,
                m.acc(field, mark, FinalAccessor, abstract = false),
                m.acc(field, mark, abstract = false),
            )
        )
    }

    @Test
    fun `case B stops at base-star when field not excluded`() {
        val m = mgr(true)
        val abstraction = BaseOnlyInitialFactAbstraction(m)
        abstraction.registerNewInitialFact(m.analyzedExcluding(mark), FactTypeChecker.Dummy)

        val produced = abstraction.addAbstractedInitialFact(m.finalOf(field, AnyAccessor, mark), FactTypeChecker.Dummy)

        val fieldAp = BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1)
        assertTrue(contains(produced, fieldAp, fieldAp))
        assertFalse(
            contains(produced, m.acc(field, abstract = true), m.acc(field, abstract = true))
        )
    }

    @Test
    fun `same added fact twice abstracts only once`() {
        val m = mgr(false)
        val abstraction = BaseOnlyInitialFactAbstraction(m)
        abstraction.registerNewInitialFact(m.analyzedExcluding(mark), FactTypeChecker.Dummy)

        val added = m.finalOf(AnyAccessor, mark)
        val first = abstraction.addAbstractedInitialFact(added, FactTypeChecker.Dummy)
        val second = abstraction.addAbstractedInitialFact(added, FactTypeChecker.Dummy)

        assertTrue(first.isNotEmpty())
        assertTrue(second.isEmpty())
    }

    @Test
    fun `mark-less value on a static abstracts to a covering final never open`() {
        val m = mgr(false)
        val stat = ClassStaticAccessor("S")
        val abstraction = BaseOnlyInitialFactAbstraction(m)

        val valueOnStatic = BaseOnlyFinalFactAp(m, arg0, m.acc(stat, FinalAccessor, abstract = false), ExclusionSet.Empty)
        val produced = abstraction.addAbstractedInitialFact(valueOnStatic, FactTypeChecker.Dummy)

        val staticAp = BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0)
        assertTrue(contains(produced, staticAp, staticAp))
        assertTrue(produced.none { (_, final) ->
            (final as BaseOnlyFinalFactAp).access.let { !it.isEmpty && !it.hasAp && it.suffixIdx == NO_ACCESSOR }
        })
    }

    @Test
    fun `abstracting a field-abstract fact yields an open field-abstract initial not a closed value`() {
        val m = mgr(fieldSensitive = true)
        val abstraction = BaseOnlyInitialFactAbstraction(m)

        val fieldAbstract = BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1)
        val fact = BaseOnlyFinalFactAp(m, arg0, fieldAbstract, ExclusionSet.Empty)

        val produced = abstraction.addAbstractedInitialFact(fact, FactTypeChecker.Dummy)

        assertTrue(
            contains(produced, fieldAbstract, fieldAbstract),
            "a field-abstract added fact must abstract to an open field-abstract initial, got: $produced",
        )
        val closedValue = m.acc(FinalAccessor, abstract = false)
        assertFalse(
            produced.any { (initial, _) -> (initial as BaseOnlyInitialFactAp).access == closedValue },
            "a field-abstract added fact must not collapse to a closed value initial, got: $produced",
        )
    }

    @Test
    fun `ladder starts fully abstract then walks the abstraction point rightward`() {
        val m = mgr(false)
        val stat = ClassStaticAccessor("S")
        val abstraction = BaseOnlyInitialFactAbstraction(m)

        val fact = BaseOnlyFinalFactAp(m, arg0, m.acc(stat, mark, abstract = false), ExclusionSet.Empty)
        val staticAp = BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0)
        val markAp = BaseOnlyAccessOps.abstractAt(m.interner.index(stat), NO_ACCESSOR, 2)

        val first = abstraction.addAbstractedInitialFact(fact, FactTypeChecker.Dummy)
        assertTrue(contains(first, staticAp, staticAp))
        assertFalse(contains(first, markAp, markAp))

        val second = abstraction.registerNewInitialFact(m.analyzedExcluding(stat), FactTypeChecker.Dummy)
        assertTrue(contains(second, markAp, markAp))
    }

    @Test
    fun `refinement on type group keeps the type-carrying fact and abstracts it`() {
        val m = mgr(false)
        val typeInfo = TypeInfoAccessor("pkg.fn")
        val abstraction = BaseOnlyInitialFactAbstraction(m)

        val demand = m.analyzedExcluding(TypeInfoGroupAccessor)
        abstraction.registerNewInitialFact(demand, FactTypeChecker.Dummy)

        val typed = m.finalOf(TypeInfoGroupAccessor, typeInfo) as BaseOnlyFinalFactAp
        assertTrue(typed.access == m.acc(typeInfo, FinalAccessor, abstract = false))

        assertTrue(
            typed.delta(demand).any { it is BaseOnlyNodeFinalDelta },
            "excluding the info-less group must not drop the type-carrying delta",
        )

        val produced = abstraction.addAbstractedInitialFact(typed, FactTypeChecker.Dummy)
        assertTrue(contains(produced, m.acc(abstract = true), m.acc(abstract = true)))
    }

    @Test
    fun `refinement on type group after the fact emits the refined type fact`() {
        val m = mgr(false)
        val typeInfo = TypeInfoAccessor("pkg.fn")
        val abstraction = BaseOnlyInitialFactAbstraction(m)

        abstraction.addAbstractedInitialFact(m.finalOf(TypeInfoGroupAccessor, typeInfo), FactTypeChecker.Dummy)

        val produced = abstraction.registerNewInitialFact(
            m.analyzedExcluding(TypeInfoGroupAccessor), FactTypeChecker.Dummy,
        )

        val typeAp = m.acc(typeInfo, FinalAccessor, abstract = false)
        assertTrue(
            contains(produced, typeAp, typeAp),
            "excluding the info-less group must walk past the collapsed type accessor and emit .{name}.\$",
        )
    }

    @Test
    fun `refinement on the type accessor itself drops the type-carrying fact`() {
        val m = mgr(false)
        val typeInfo = TypeInfoAccessor("pkg.fn")

        val demandExcludingType = m.analyzedExcluding(typeInfo)
        val typed = m.finalOf(TypeInfoGroupAccessor, typeInfo) as BaseOnlyFinalFactAp

        assertFalse(typed.delta(demandExcludingType).any { it is BaseOnlyNodeFinalDelta })
    }

    @Test
    fun `delta drops a suffix whose head is excluded by the initial fact`() {
        val m = mgr(false)
        val final = m.finalOf(AnyAccessor, mark)
        val initialNoExclusion = m.mostAbstractInitialAp(arg0).prependAccessor(AnyAccessor)
        val initialExcludingMark = initialNoExclusion.exclude(mark)

        assertTrue(final.delta(initialNoExclusion).any { !it.isEmpty })
        assertTrue(final.delta(initialExcludingMark).none { it is BaseOnlyNodeFinalDelta })
    }

    private fun assertNoMixedEdge(produced: List<Pair<InitialFactAp, FinalFactAp>>) {
        assertTrue(
            produced.none { (initial, final) ->
                (initial as BaseOnlyInitialFactAp); (final as BaseOnlyFinalFactAp)
                !initial.access.hasAp && final.access.hasAp
            },
            "no F2F edge may have a concrete initial and an abstract final, got $produced",
        )
    }

    @Test
    fun `bare-value seed emits concrete identity and abstract identity, never the mixed edge`() {
        val m = mgr(false)
        val abstraction = BaseOnlyInitialFactAbstraction(m)
        val produced = abstraction.addAbstractedInitialFact(
            BaseOnlyFinalFactAp(m, arg0, m.acc(FinalAccessor, abstract = false), ExclusionSet.Empty),
            FactTypeChecker.Dummy,
        )
        val concrete = m.acc(FinalAccessor, abstract = false)
        val abstract = m.acc(abstract = true)
        assertTrue(contains(produced, concrete, concrete), "expected prefix.\$ => prefix.\$, got $produced")
        assertTrue(contains(produced, abstract, abstract), "expected prefix.* => prefix.*, got $produced")
        assertNoMixedEdge(produced)
    }

    @Test
    fun `static-only value seed never emits a concrete-to-abstract edge`() {
        val m = mgr(false)
        val stat = ClassStaticAccessor("S")
        val abstraction = BaseOnlyInitialFactAbstraction(m)
        abstraction.addAbstractedInitialFact(
            BaseOnlyFinalFactAp(m, arg0, m.acc(stat, FinalAccessor, abstract = false), ExclusionSet.Empty),
            FactTypeChecker.Dummy,
        )
        val produced = abstraction.registerNewInitialFact(m.analyzedExcluding(stat), FactTypeChecker.Dummy)
        assertNoMixedEdge(produced)
        val concrete = m.acc(stat, FinalAccessor, abstract = false)
        assertTrue(contains(produced, concrete, concrete), "static-only terminal must emit the concrete identity, got $produced")
    }

    @Test
    fun `field-only value seed never emits a concrete-to-abstract edge`() {
        val m = mgr(fieldSensitive = true)
        val abstraction = BaseOnlyInitialFactAbstraction(m)
        abstraction.addAbstractedInitialFact(
            BaseOnlyFinalFactAp(m, arg0, m.acc(field, FinalAccessor, abstract = false), ExclusionSet.Empty),
            FactTypeChecker.Dummy,
        )
        val produced = abstraction.registerNewInitialFact(m.analyzedExcluding(field), FactTypeChecker.Dummy)
        assertNoMixedEdge(produced)
        val concrete = m.acc(field, FinalAccessor, abstract = false)
        assertTrue(contains(produced, concrete, concrete), "field-only terminal must emit the concrete identity, got $produced")
    }
}
