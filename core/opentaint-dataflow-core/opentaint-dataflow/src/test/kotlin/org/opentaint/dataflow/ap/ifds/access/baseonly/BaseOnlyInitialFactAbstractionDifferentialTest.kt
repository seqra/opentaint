package org.opentaint.dataflow.ap.ifds.access.baseonly

import kotlinx.collections.immutable.persistentHashSetOf
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.VALUE_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTypeInfoAccessor
import org.opentaint.dataflow.util.Cancellation
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals

class BaseOnlyInitialFactAbstractionDifferentialTest {
    @Test
    fun `an exclusion with no matching active blocker emits nothing`() {
        val manager = manager()
        val indexed = BaseOnlyInitialFactAbstraction(manager)
        val linear = LinearInitialFactAbstraction(manager)
        val field = FieldAccessor("Owner", "blocked", "Value")
        val unrelated = TaintMarkAccessor("unrelated")

        assertEquivalent(
            Add(finalFact(manager, manager.interner.index(field), FINAL_ACCESSOR_IDX)),
            indexed,
            linear,
        )
        val output = assertEquivalent(
            Register(demand(manager, setOf(unrelated))),
            indexed,
            linear,
        )

        assertEquals(emptySet(), output)
    }

    @Test
    fun `only facts blocked by an added exclusion advance`() {
        val manager = manager()
        val indexed = BaseOnlyInitialFactAbstraction(manager)
        val linear = LinearInitialFactAbstraction(manager)
        val first = TaintMarkAccessor("first")
        val second = TaintMarkAccessor("second")
        val firstAccess = packBaseOnlyAccess(
            NO_ACCESSOR, NO_ACCESSOR, manager.interner.index(first), BaseOnlyValueAccessorState.Normal,
        )
        val secondAccess = packBaseOnlyAccess(
            NO_ACCESSOR, NO_ACCESSOR, manager.interner.index(second), BaseOnlyValueAccessorState.Normal,
        )

        assertEquivalent(Add(finalFact(manager, access = firstAccess)), indexed, linear)
        assertEquivalent(Add(finalFact(manager, access = secondAccess)), indexed, linear)
        val output = assertEquivalent(Register(demand(manager, setOf(first))), indexed, linear)

        assertEquals(
            setOf(EdgeKey(AccessPathBase.This, firstAccess, firstAccess)),
            output,
            "the unrelated second blocker must remain pending",
        )
    }

    @Test
    fun `type group and concrete type blocker indices cannot emit the same fact twice`() {
        val manager = manager()
        val indexed = BaseOnlyInitialFactAbstraction(manager)
        val linear = LinearInitialFactAbstraction(manager)
        val type = TypeInfoAccessor("pkg.Type")
        val typeAccess = packBaseOnlyAccess(
            NO_ACCESSOR, NO_ACCESSOR, manager.interner.index(type), BaseOnlyValueAccessorState.Normal,
        )

        assertEquivalent(Add(finalFact(manager, access = typeAccess)), indexed, linear)
        val unblockedByGroup = assertEquivalent(
            Register(demand(manager, setOf(TypeInfoGroupAccessor))),
            indexed,
            linear,
        )
        assertEquals(setOf(EdgeKey(AccessPathBase.This, typeAccess, typeAccess)), unblockedByGroup)

        val duplicate = assertEquivalent(Register(demand(manager, setOf(type))), indexed, linear)
        assertEquals(emptySet(), duplicate, "unblocking through the dual concrete index must not re-emit the fact")
    }

    @Test
    fun `indexed abstraction agrees with a linear rescan reference over random operation sequences`() {
        repeat(SEEDS) { seed ->
            val manager = BaseOnlyApManager(
                AnyAccessorUnrollStrategy.AnyAccessorDisabled,
                Cancellation(),
                fieldSensitive = true,
            )
            val indexed = BaseOnlyInitialFactAbstraction(manager)
            val linear = LinearInitialFactAbstraction(manager)
            val fixture = Fixture(manager)
            val random = Random(seed)

            repeat(STEPS_PER_SEED) { step ->
                val operation = fixture.randomOperation(random)
                val expected = operation.apply(linear)
                val actual = operation.apply(indexed)
                assertEquals(
                    expected.toEdgeKeys(),
                    actual.toEdgeKeys(),
                    "seed=$seed, step=$step, operation=$operation",
                )
            }
        }
    }

    private fun manager() = BaseOnlyApManager(
        AnyAccessorUnrollStrategy.AnyAccessorDisabled,
        Cancellation(),
        fieldSensitive = true,
    )

    private fun finalFact(
        manager: BaseOnlyApManager,
        fieldIdx: Int = NO_ACCESSOR,
        suffixIdx: Int = FINAL_ACCESSOR_IDX,
        access: BaseOnlyAccess = packBaseOnlyAccess(fieldIdx = fieldIdx, staticIdx = NO_ACCESSOR, suffixIdx = suffixIdx),
    ) = BaseOnlyFinalFactAp(manager, AccessPathBase.This, access, ExclusionSet.Empty)

    private fun demand(manager: BaseOnlyApManager, exclusions: Set<Accessor>) = BaseOnlyInitialFactAp(
        manager,
        AccessPathBase.This,
        ABSTRACT_EMPTY_ACCESS,
        ExclusionSet.Concrete(persistentHashSetOf(*exclusions.toTypedArray())),
    )

    private fun assertEquivalent(
        operation: Operation,
        indexed: BaseOnlyInitialFactAbstraction,
        linear: LinearInitialFactAbstraction,
    ): Set<EdgeKey> {
        val expected = operation.apply(linear).toEdgeKeys()
        val actual = operation.apply(indexed).toEdgeKeys()
        assertEquals(expected, actual, "operation=$operation")
        return actual
    }

    private class Fixture(private val manager: BaseOnlyApManager) {
        private val bases = listOf(AccessPathBase.This, AccessPathBase.Argument(0), AccessPathBase.Argument(1))
        private val statics = List(3) { ClassStaticAccessor("Owner$it") }
        private val fields = List(5) { FieldAccessor("Owner", "field$it", "Value") }
        private val marks = List(5) { TaintMarkAccessor("mark$it") }
        private val types = List(3) { TypeInfoAccessor("pkg.Type$it") }
        private val possibleExclusions: List<Accessor> =
            statics + fields + ElementAccessor + marks + types + TypeInfoGroupAccessor + ValueAccessor

        private val staticIndices = statics.map(manager.interner::index)
        private val fieldIndices = fields.map(manager.interner::index)
        private val markIndices = marks.map(manager.interner::index)
        private val typeIndices = types.map(manager.interner::index)

        fun randomOperation(random: Random): Operation =
            if (random.nextInt(100) < 48) randomAdd(random) else randomRegister(random)

        private fun randomAdd(random: Random): Operation {
            val base = bases.random(random)
            val staticIdx = if (random.nextInt(4) == 0) staticIndices.random(random) else NO_ACCESSOR
            val fieldIdx = when (random.nextInt(4)) {
                0 -> fieldIndices.random(random)
                1 -> ELEMENT_ACCESSOR_IDX
                else -> NO_ACCESSOR
            }
            val suffixIdx = when (random.nextInt(5)) {
                0 -> FINAL_ACCESSOR_IDX
                1, 2 -> markIndices.random(random)
                else -> typeIndices.random(random)
            }
            val valueState = if (
                suffixIdx != FINAL_ACCESSOR_IDX && random.nextBoolean()
            ) {
                BaseOnlyValueAccessorState.Value
            } else {
                BaseOnlyValueAccessorState.Normal
            }
            val access = packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx, valueState)
            return Add(BaseOnlyFinalFactAp(manager, base, access, ExclusionSet.Empty))
        }

        private fun randomRegister(random: Random): Operation {
            val base = bases.random(random)
            val staticIdx = if (random.nextBoolean()) staticIndices.random(random) else NO_ACCESSOR
            val fieldIdx = if (random.nextBoolean()) fieldIndices.random(random) else NO_ACCESSOR
            val pattern = when (random.nextInt(7)) {
                0 -> ABSTRACT_EMPTY_ACCESS
                1 -> BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0)
                2 -> BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1)
                3 -> BaseOnlyAccessOps.abstractAt(staticIdx, NO_ACCESSOR, 1)
                4 -> BaseOnlyAccessOps.abstractAt(staticIdx, NO_ACCESSOR, 2)
                5 -> BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, fieldIdx, 2)
                else -> BaseOnlyAccessOps.abstractAt(staticIdx, fieldIdx, 2)
            }
            val count = random.nextInt(1, 5)
            val excluded = buildSet {
                repeat(count) { add(possibleExclusions.random(random)) }
            }
            val exclusions = ExclusionSet.Concrete(persistentHashSetOf(*excluded.toTypedArray()))
            return Register(BaseOnlyInitialFactAp(manager, base, pattern, exclusions))
        }
    }

    private sealed interface Operation {
        fun apply(abstraction: InitialFactAbstractionFacade): List<Pair<InitialFactAp, FinalFactAp>>
        fun apply(abstraction: BaseOnlyInitialFactAbstraction): List<Pair<InitialFactAp, FinalFactAp>>
    }

    private data class Add(val fact: BaseOnlyFinalFactAp) : Operation {
        override fun apply(abstraction: InitialFactAbstractionFacade) = abstraction.add(fact)
        override fun apply(abstraction: BaseOnlyInitialFactAbstraction) =
            abstraction.addAbstractedInitialFact(fact, FactTypeChecker.Dummy)
    }

    private data class Register(val fact: BaseOnlyInitialFactAp) : Operation {
        override fun apply(abstraction: InitialFactAbstractionFacade) = abstraction.register(fact)
        override fun apply(abstraction: BaseOnlyInitialFactAbstraction) =
            abstraction.registerNewInitialFact(fact, FactTypeChecker.Dummy)
    }

    private interface InitialFactAbstractionFacade {
        fun add(fact: BaseOnlyFinalFactAp): List<Pair<InitialFactAp, FinalFactAp>>
        fun register(fact: BaseOnlyInitialFactAp): List<Pair<InitialFactAp, FinalFactAp>>
    }

    /**
     * Deliberately has no blocker index. Every exclusion change rescans every added fact, making
     * this a small, independent semantic oracle for the indexed implementation.
     */
    private class LinearInitialFactAbstraction(
        private val manager: BaseOnlyApManager,
    ) : InitialFactAbstractionFacade {
        private val perBase = mutableMapOf<AccessPathBase, BaseState>()

        private class BaseState {
            val added = linkedSetOf<BaseOnlyAccess>()
            val emitted = mutableSetOf<BaseOnlyAccess>()
            val exclusionsByPattern = mutableMapOf<BaseOnlyAccess, MutableSet<Int>>()
        }

        override fun add(fact: BaseOnlyFinalFactAp): List<Pair<InitialFactAp, FinalFactAp>> {
            val state = perBase.getOrPut(fact.base, ::BaseState)
            if (!state.added.add(fact.access)) return emptyList()
            return buildList { abstract(fact.base, fact.access, state, this) }
        }

        override fun register(fact: BaseOnlyInitialFactAp): List<Pair<InitialFactAp, FinalFactAp>> {
            val state = perBase.getOrPut(fact.base, ::BaseState)
            val incoming = when (val exclusions = fact.exclusions) {
                ExclusionSet.Empty -> emptySet()
                ExclusionSet.Universe -> error("Unexpected universe exclusion")
                is ExclusionSet.Concrete -> exclusions.set.mapTo(mutableSetOf(), manager.interner::index)
            }
            val known = state.exclusionsByPattern.getOrPut(fact.access) { mutableSetOf() }
            if (!known.addAll(incoming)) return emptyList()

            return buildList {
                state.added.forEach { access -> abstract(fact.base, access, state, this) }
            }
        }

        private fun abstract(
            base: AccessPathBase,
            added: BaseOnlyAccess,
            state: BaseState,
            output: MutableList<Pair<InitialFactAp, FinalFactAp>>,
        ) {
            val prefix = mutableListOf<Int>()
            val core = buildList {
                if (added.staticIdx >= 0) add(added.staticIdx)
                if (added.fieldIdx >= 0) add(added.fieldIdx)
                if (added.hasSemanticMark && added.valueAccessorState == BaseOnlyValueAccessorState.Value) {
                    add(if (added.hasTypeInfoSuffix) TYPE_INFO_GROUP_ACCESSOR_IDX else VALUE_ACCESSOR_IDX)
                }
                if (added.suffixIdx >= 0 && added.suffixIdx != FINAL_ACCESSOR_IDX) add(added.suffixIdx)
            }

            for (accessor in core) {
                val apSlot = slotOfIdx(accessor)
                val blockedAt = abstractAccess(prefix, apSlot)
                emitIdentity(base, blockedAt, state, output)
                if (!state.excludes(blockedAt, accessor)) return
                prefix.add(accessor)
            }

            if (added.hasAp) {
                emitIdentity(base, abstractAccess(prefix, added.apSlot), state, output)
            } else {
                emitIdentity(base, abstractAccess(prefix, 2), state, output)
                var concrete = BaseOnlyAccessOps.build(
                    (prefix + FINAL_ACCESSOR_IDX).toIntArray(),
                    isAbstract = false,
                )
                if (concrete.hasSemanticMark) {
                    concrete = concrete.withValueAccessorState(added.valueAccessorState)
                }
                emitIdentity(base, concrete, state, output)
            }
        }

        private fun BaseState.excludes(blockedAt: BaseOnlyAccess, accessor: Int): Boolean =
            exclusionsByPattern.any { (pattern, exclusions) ->
                (pattern == ABSTRACT_EMPTY_ACCESS || BaseOnlyAccessOps.containsAccess(pattern, blockedAt)) &&
                    (accessor in exclusions ||
                        accessor.isTypeInfoAccessor() && TYPE_INFO_GROUP_ACCESSOR_IDX in exclusions)
            }

        private fun abstractAccess(prefix: List<Int>, apSlot: Int): BaseOnlyAccess {
            var staticIdx = NO_ACCESSOR
            var fieldIdx = NO_ACCESSOR
            prefix.forEach { idx ->
                when {
                    idx.isStaticAccessor() -> staticIdx = idx
                    idx.isFieldAccessor() || idx == ELEMENT_ACCESSOR_IDX -> fieldIdx = idx
                }
            }
            return BaseOnlyAccessOps.abstractAt(staticIdx, fieldIdx, apSlot)
        }

        private fun emitIdentity(
            base: AccessPathBase,
            access: BaseOnlyAccess,
            state: BaseState,
            output: MutableList<Pair<InitialFactAp, FinalFactAp>>,
        ) {
            if (!state.emitted.add(access)) return
            output += BaseOnlyInitialFactAp(manager, base, access, ExclusionSet.Empty) to
                BaseOnlyFinalFactAp(manager, base, access, ExclusionSet.Empty)
        }
    }

    private data class EdgeKey(
        val base: AccessPathBase,
        val initial: BaseOnlyAccess,
        val final: BaseOnlyAccess,
    )

    private fun List<Pair<InitialFactAp, FinalFactAp>>.toEdgeKeys(): Set<EdgeKey> = mapTo(mutableSetOf()) { (i, f) ->
        i as BaseOnlyInitialFactAp
        f as BaseOnlyFinalFactAp
        EdgeKey(i.base, i.access, f.access)
    }

    private companion object {
        const val SEEDS = 64
        const val STEPS_PER_SEED = 300
    }
}
