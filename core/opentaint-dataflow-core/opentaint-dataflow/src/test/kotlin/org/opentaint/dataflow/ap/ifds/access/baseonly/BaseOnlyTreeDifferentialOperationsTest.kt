package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.AccessorList
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.ReadableAccessorList
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.ap.ifds.serialization.ApSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.CommonMethod
import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

/**
 * Executable Tree conformance for BaseOnly operations.
 *
 * These tests deliberately compare observable path languages rather than packed representations:
 * BaseOnly is allowed to widen a Tree result, but every sequence readable from Tree must remain
 * readable from at least one corresponding BaseOnly result.
 */
class BaseOnlyTreeDifferentialOperationsTest {
    private val base = AccessPathBase.Argument(0)
    private val stat = ClassStaticAccessor("example.Owner")
    private val field = FieldAccessor("example.Owner", "value", "example.Value")
    private val otherField = FieldAccessor("example.Value", "next", "example.Result")
    private val mark = TaintMarkAccessor("source")
    private val typeInfo = TypeInfoAccessor("example.Owner#getValue")

    private val unrollStructural = object : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            AnyAccessor.containsAccessor(accessor)
    }

    private fun managers(): Pair<TreeApManager, BaseOnlyApManager> =
        TreeApManager(unrollStructural, RefManager(), Cancellation()) to
            BaseOnlyApManager(unrollStructural, Cancellation(), fieldSensitive = true)

    private fun ApManager.finalOf(vararg accessors: Accessor): FinalFactAp {
        var fact = createFinalAp(base, ExclusionSet.Empty)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun ApManager.abstractInitialOf(vararg accessors: Accessor): InitialFactAp {
        var fact = mostAbstractInitialAp(base)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun ApManager.abstractFinalOf(vararg accessors: Accessor): FinalFactAp {
        var fact = mostAbstractFinalAp(base)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun ApManager.finalInitialOf(vararg accessors: Accessor): InitialFactAp {
        var fact = createFinalInitialAp(base, ExclusionSet.Empty)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private val observations: List<List<Accessor>> by lazy {
        val alphabet = listOf(
            stat,
            field,
            otherField,
            ElementAccessor,
            AnyAccessor,
            ValueAccessor,
            mark,
            TypeInfoGroupAccessor,
            typeInfo,
            FinalAccessor,
        )
        buildList {
            add(emptyList())
            var frontier = listOf(emptyList<Accessor>())
            repeat(4) {
                frontier = frontier.flatMap { prefix -> alphabet.map { prefix + it } }
                addAll(frontier)
            }
        }
    }

    private fun readable(list: ReadableAccessorList<*>, sequence: List<Accessor>): Boolean {
        var current: ReadableAccessorList<*> = list
        for (accessor in sequence) {
            current = current.readAccessor(accessor) as? ReadableAccessorList<*> ?: return false
        }
        return true
    }

    private fun assertOverapproximates(
        treeResults: Collection<ReadableAccessorList<*>>,
        baseOnlyResults: Collection<ReadableAccessorList<*>>,
        scenario: String,
    ) {
        for (sequence in observations) {
            if (treeResults.none { readable(it, sequence) }) continue
            assertTrue(
                baseOnlyResults.any { readable(it, sequence) },
                "$scenario lost readable sequence ${sequence.joinToString(" -> ")}",
            )
        }
    }

    private fun assertReadAndStartConformance(
        tree: ReadableAccessorList<*>,
        baseOnly: ReadableAccessorList<*>,
        scenario: String,
    ) {
        val probes = listOf(
            stat,
            field,
            otherField,
            ElementAccessor,
            AnyAccessor,
            ValueAccessor,
            mark,
            typeInfo,
            FinalAccessor,
        )
        for (probe in probes) {
            assertEquals(
                baseOnly.readAccessor(probe) != null,
                baseOnly.startsWithAccessor(probe),
                "$scenario: BaseOnly read/startsWith disagree for $probe",
            )
            if (tree.readAccessor(probe) != null) {
                assertNotNull(baseOnly.readAccessor(probe), "$scenario lost Tree read for $probe")
            }
            if (tree.startsWithAccessor(probe)) {
                assertTrue(baseOnly.startsWithAccessor(probe), "$scenario lost Tree start for $probe")
            }
        }

        for (treeStart in tree.getStartAccessors()) {
            val represented = treeStart in baseOnly.getStartAccessors() ||
                (AnyAccessor.containsAccessor(treeStart) && AnyAccessor in baseOnly.getStartAccessors())
            assertTrue(represented, "$scenario lost symbolic Tree start edge $treeStart")
        }
    }

    @Test
    fun `prepend composes with read startsWith and accessor views without losing Tree paths`() {
        val (treeManager, baseOnlyManager) = managers()
        var tree = treeManager.finalOf(AnyAccessor, mark)
        var baseOnly = baseOnlyManager.finalOf(AnyAccessor, mark)

        fun verify(stage: String) {
            assertOverapproximates(listOf(tree), listOf(baseOnly), stage)
            assertReadAndStartConformance(tree, baseOnly, stage)
            assertFalse(AnyAccessor in tree.getAllAccessors(), "$stage: Tree all-accessor view exposed Any")
            assertFalse(AnyAccessor in baseOnly.getAllAccessors(), "$stage: BaseOnly all-accessor view exposed Any")
        }

        verify("any-mark suffix")
        assertTrue(AnyAccessor in tree.getStartAccessors())
        assertTrue(AnyAccessor in baseOnly.getStartAccessors())

        tree = tree.prependAccessor(field)
        baseOnly = baseOnly.prependAccessor(field)
        verify("field prepend")

        tree = tree.prependAccessor(stat)
        baseOnly = baseOnly.prependAccessor(stat)
        verify("static prepend")
    }

    @Test
    fun `construction with two fields retains the outer field and covers the inner Tree path`() {
        val (treeManager, baseOnlyManager) = managers()
        val tree = treeManager.finalOf(field, otherField, mark)
        val baseOnly = baseOnlyManager.finalOf(field, otherField, mark)

        assertOverapproximates(listOf(tree), listOf(baseOnly), "two-field construction")
        assertTrue(baseOnly.startsWithAccessor(field))
        val afterOuter = assertNotNull(baseOnly.readAccessor(field))
        assertTrue(afterOuter.startsWithAccessor(otherField), "discarded inner field must be covered by Any")
    }

    @Test
    fun `Tree Any is a start edge but never an all-accessor value`() {
        val (treeManager, baseOnlyManager) = managers()
        val tree = treeManager.finalOf(AnyAccessor, mark)
        val baseOnly = baseOnlyManager.finalOf(AnyAccessor, mark)

        assertEquals(setOf(AnyAccessor), tree.getStartAccessors())
        assertTrue(AnyAccessor in baseOnly.getStartAccessors())
        assertFalse(AnyAccessor in tree.getAllAccessors())
        assertFalse(AnyAccessor in baseOnly.getAllAccessors())
        assertTrue(mark in tree.getAllAccessors())
        assertTrue(mark in baseOnly.getAllAccessors())
    }

    @Test
    fun `type-info logical views and reads overapproximate Tree`() {
        val (treeManager, baseOnlyManager) = managers()
        val tree = treeManager.finalOf(TypeInfoGroupAccessor, typeInfo)
        val baseOnly = baseOnlyManager.finalOf(TypeInfoGroupAccessor, typeInfo)

        assertOverapproximates(listOf(tree), listOf(baseOnly), "type-info")
        assertReadAndStartConformance(tree, baseOnly, "type-info")
        assertTrue(TypeInfoGroupAccessor in baseOnly.getStartAccessors())
        assertTrue(
            baseOnly.getAllAccessors().containsAll(tree.getAllAccessors()),
            "BaseOnly logical all-accessor view lost ${tree.getAllAccessors() - baseOnly.getAllAccessors()}",
        )
        assertEquals(baseOnly, baseOnly.clearAccessor(TypeInfoGroupAccessor))
        assertEquals(baseOnly, baseOnly.clearAccessor(typeInfo))
    }

    @Test
    fun `build and prepend preserve Value then taint mark composite suffix`() {
        val (treeManager, baseOnlyManager) = managers()
        val tree = treeManager.finalOf(ValueAccessor, mark)
        val baseOnly = baseOnlyManager.finalOf(ValueAccessor, mark)
        val builtAccess = BaseOnlyAccessOps.build(
            intArrayOf(
                baseOnlyManager.interner.index(ValueAccessor),
                baseOnlyManager.interner.index(mark),
                baseOnlyManager.interner.index(FinalAccessor),
            ),
            isAbstract = false,
        )
        val builtBaseOnly = BaseOnlyFinalFactAp(baseOnlyManager, base, builtAccess, ExclusionSet.Empty)

        assertOverapproximates(listOf(tree), listOf(baseOnly), "Value -> mark -> final")
        assertOverapproximates(listOf(tree), listOf(builtBaseOnly), "build(Value -> mark -> final)")
        assertReadAndStartConformance(tree, baseOnly, "Value -> mark -> final")
        assertTrue(ValueAccessor in baseOnly.getStartAccessors())
        assertTrue(ValueAccessor in baseOnly.getAllAccessors())
        val afterValue = assertNotNull(baseOnly.readAccessor(ValueAccessor))
        assertTrue(afterValue.startsWithAccessor(mark), "reading Value must retain the following mark")
    }

    @Test
    fun `joining normal and value states retains two facts`() {
        val (treeManager, baseOnlyManager) = managers()
        val treeNormal = treeManager.finalOf(mark) as AccessTree
        val treeValue = treeManager.finalOf(ValueAccessor, mark) as AccessTree
        val treeUnion = AccessTree(
            treeManager,
            base,
            treeNormal.access.mergeAdd(treeValue.access),
            ExclusionSet.Empty,
        )
        val normal = baseOnlyManager.finalOf(mark) as BaseOnlyFinalFactAp
        val value = baseOnlyManager.finalOf(ValueAccessor, mark) as BaseOnlyFinalFactAp
        val joined = canonicalJoin(normal.access, value.access).map { access ->
            BaseOnlyFinalFactAp(baseOnlyManager, base, access, ExclusionSet.Empty)
        }

        assertEquals(
            setOf(BaseOnlyValueAccessorState.Normal, BaseOnlyValueAccessorState.Value),
            joined.mapTo(hashSetOf()) { it.access.valueAccessorState },
        )
        assertOverapproximates(listOf(treeUnion), joined, "joined value-accessor states")
        assertEquals(
            setOf(AnyAccessor, ValueAccessor, mark),
            joined.flatMapTo(hashSetOf()) { it.getStartAccessors() },
        )
        assertTrue(joined.flatMapTo(hashSetOf()) { it.getAllAccessors() }.containsAll(treeUnion.getAllAccessors()))

        val treeAfterValue = assertNotNull(treeUnion.readAccessor(ValueAccessor))
        val baseOnlyAfterValue = joined.mapNotNull { it.readAccessor(ValueAccessor) }
        assertOverapproximates(listOf(treeAfterValue), baseOnlyAfterValue, "Value read ValueAccessor")
        assertTrue(
            baseOnlyAfterValue.filterIsInstance<BaseOnlyFinalFactAp>()
                .all { it.access.valueAccessorState == BaseOnlyValueAccessorState.Normal },
        )

        val treeNormalInitial = treeManager.finalInitialOf(mark)
        val treeValueInitial = treeManager.finalInitialOf(ValueAccessor, mark)
        val normalInitial = baseOnlyManager.finalInitialOf(mark)
        val valueInitial = baseOnlyManager.finalInitialOf(ValueAccessor, mark)
        assertTrue(treeUnion.contains(treeNormalInitial))
        assertTrue(treeUnion.contains(treeValueInitial))
        assertTrue(joined.any { it.contains(normalInitial) })
        assertTrue(joined.any { it.contains(valueInitial) })

        val treeInitial = treeManager.mostAbstractInitialAp(base)
        val baseOnlyInitial = baseOnlyManager.mostAbstractInitialAp(base)
        val treeTarget = treeManager.mostAbstractFinalAp(base)
        val baseOnlyTarget = baseOnlyManager.mostAbstractFinalAp(base)
        val treeResults = treeUnion.delta(treeInitial).mapNotNull { treeTarget.concat(FactTypeChecker.Dummy, it) }
        val baseOnlyResults = joined.flatMap { fact ->
            fact.delta(baseOnlyInitial).mapNotNull { baseOnlyTarget.concat(FactTypeChecker.Dummy, it) }
        }
        assertOverapproximates(treeResults, baseOnlyResults, "two-state delta + concat")
        assertEquals(
            setOf(BaseOnlyValueAccessorState.Normal, BaseOnlyValueAccessorState.Value),
            baseOnlyResults.filterIsInstance<BaseOnlyFinalFactAp>()
                .mapTo(hashSetOf()) { it.access.valueAccessorState },
        )
    }

    @Test
    fun `final delta then concat overapproximates the corresponding Tree scenario`() {
        val (treeManager, baseOnlyManager) = managers()
        val treeSource = treeManager.finalOf(field, AnyAccessor, mark)
        val baseOnlySource = baseOnlyManager.finalOf(field, AnyAccessor, mark)
        val treeInitial = treeManager.abstractInitialOf(field, AnyAccessor)
        val baseOnlyInitial = baseOnlyManager.abstractInitialOf(field, AnyAccessor)
        val treeTarget = treeManager.abstractFinalOf(field, AnyAccessor)
        val baseOnlyTarget = baseOnlyManager.abstractFinalOf(field, AnyAccessor)

        val treeResults = treeSource.delta(treeInitial).mapNotNull {
            treeTarget.concat(FactTypeChecker.Dummy, it)
        }
        val baseOnlyResults = baseOnlySource.delta(baseOnlyInitial).mapNotNull {
            baseOnlyTarget.concat(FactTypeChecker.Dummy, it)
        }

        assertTrue(treeResults.isNotEmpty(), "Tree scenario must exercise delta + concat")
        assertTrue(baseOnlyResults.isNotEmpty(), "BaseOnly rejected a Tree-applicable delta + concat scenario")
        assertOverapproximates(treeResults, baseOnlyResults, "delta + concat")
    }

    @Test
    fun `final concat widens an extra structural delta and covers Tree`() {
        val (treeManager, baseOnlyManager) = managers()
        val treeTarget = treeManager.abstractFinalOf(field)
        val baseOnlyTarget = baseOnlyManager.abstractFinalOf(field)

        for (suffix in listOf(listOf<Accessor>(otherField), listOf(otherField, mark))) {
            val treeDelta = treeManager.finalOf(*suffix.toTypedArray())
                .delta(treeManager.mostAbstractInitialAp(base))
                .single()
            val baseOnlyDelta = BaseOnlyNodeFinalDelta(
                baseOnlyManager,
                (baseOnlyManager.finalOf(*suffix.toTypedArray()) as BaseOnlyFinalFactAp).access,
            )

            val treeResult = assertNotNull(treeTarget.concat(FactTypeChecker.Dummy, treeDelta))
            val baseOnlyResult = assertNotNull(baseOnlyTarget.concat(FactTypeChecker.Dummy, baseOnlyDelta))

            assertEquals(setOf(field), baseOnlyResult.getStartAccessors())
            assertTrue(treeResult.startsWithAccessor(field))
            if (suffix.last() == mark) {
                assertTrue(baseOnlyResult.startsWithAccessor(field))
                val afterOuter = assertNotNull(baseOnlyResult.readAccessor(field))
                val afterInner = assertNotNull(afterOuter.readAccessor(otherField))
                assertTrue(afterInner.startsWithAccessor(mark), "absorbing inner field must preserve terminal")
                assertEquals(baseOnlyManager.finalOf(field, mark), baseOnlyResult)
            } else {
                assertTrue(baseOnlyResult.isAbstract(), "an exact field-only suffix has no terminal to retain")
                assertEquals(baseOnlyTarget, baseOnlyResult)
            }
        }
    }

    @Test
    fun `final concat follows Tree path-filter semantics`() {
        val (treeManager, baseOnlyManager) = managers()
        val treeTarget = treeManager.abstractFinalOf(field)
        val baseOnlyTarget = baseOnlyManager.abstractFinalOf(field)
        val treeDelta = treeManager.finalOf(mark)
            .delta(treeManager.mostAbstractInitialAp(base))
            .single()
        val baseOnlyDelta = BaseOnlyNodeFinalDelta(
            baseOnlyManager,
            (baseOnlyManager.finalOf(mark) as BaseOnlyFinalFactAp).access,
        )

        val acceptPathRejectCompatibility = object : FactTypeChecker {
            override fun filterFactByLocalType(actualType: org.opentaint.ir.api.common.CommonType?, factAp: FinalFactAp): FinalFactAp? = factAp
            override fun accessPathFilter(accessPath: List<Accessor>): FactTypeChecker.FactApFilter =
                FactTypeChecker.AlwaysAcceptFilter
            override fun accessPathCompatibilityFilter(accessPath: List<Accessor>): FactTypeChecker.FactCompatibilityFilter =
                object : FactTypeChecker.FactCompatibilityFilter {
                    override fun check(accessor: Accessor): FactTypeChecker.CompatibilityFilterResult =
                        FactTypeChecker.CompatibilityFilterResult.NotCompatible
                }
        }
        val acceptedTree = assertNotNull(treeTarget.concat(acceptPathRejectCompatibility, treeDelta))
        val acceptedBaseOnly = assertNotNull(baseOnlyTarget.concat(acceptPathRejectCompatibility, baseOnlyDelta))
        assertOverapproximates(listOf(acceptedTree), listOf(acceptedBaseOnly), "concat path filter acceptance")

        val rejectFinal = object : FactTypeChecker.FactApFilter {
            override fun check(accessor: Accessor): FactTypeChecker.FilterResult =
                if (accessor == FinalAccessor) FactTypeChecker.FilterResult.Reject
                else FactTypeChecker.FilterResult.Accept
        }
        val statefulReject = object : FactTypeChecker {
            override fun filterFactByLocalType(actualType: org.opentaint.ir.api.common.CommonType?, factAp: FinalFactAp): FinalFactAp? = factAp
            override fun accessPathFilter(accessPath: List<Accessor>): FactTypeChecker.FactApFilter =
                object : FactTypeChecker.FactApFilter {
                    override fun check(accessor: Accessor): FactTypeChecker.FilterResult =
                        if (accessor == mark) FactTypeChecker.FilterResult.FilterNext(rejectFinal)
                        else FactTypeChecker.FilterResult.Reject
                }
            override fun accessPathCompatibilityFilter(accessPath: List<Accessor>): FactTypeChecker.FactCompatibilityFilter =
                FactTypeChecker.AlwaysCompatibleFilter
        }

        assertNull(treeTarget.concat(statefulReject, treeDelta))
        assertNull(baseOnlyTarget.concat(statefulReject, baseOnlyDelta))
    }

    @Test
    fun `initial split delta then concat overapproximates the corresponding Tree scenario`() {
        val (treeManager, baseOnlyManager) = managers()
        val treeCaller = treeManager.abstractInitialOf(field, AnyAccessor)
        val baseOnlyCaller = baseOnlyManager.abstractInitialOf(field, AnyAccessor)
        val treeSummaryFinal = treeManager.abstractFinalOf(field)
        val baseOnlySummaryFinal = baseOnlyManager.abstractFinalOf(field)

        val treeResults = treeCaller.splitDelta(treeSummaryFinal).map { (matched, delta) ->
            matched.concat(delta)
        }
        val baseOnlyResults = baseOnlyCaller.splitDelta(baseOnlySummaryFinal).map { (matched, delta) ->
            matched.concat(delta)
        }

        assertTrue(treeResults.isNotEmpty(), "Tree scenario must exercise splitDelta + concat")
        assertTrue(baseOnlyResults.isNotEmpty(), "BaseOnly rejected a Tree-applicable splitDelta + concat scenario")
        assertOverapproximates(treeResults, baseOnlyResults, "splitDelta + concat")
    }

    @Test
    fun `root suffix concat covers both plain and implicit Any Tree prefixes`() {
        val (treeManager, baseOnlyManager) = managers()
        val treeDelta = treeManager.finalOf(otherField, mark)
            .delta(treeManager.mostAbstractInitialAp(base))
            .single()
        val baseOnlyDelta = BaseOnlyNodeFinalDelta(
            baseOnlyManager,
            (baseOnlyManager.finalOf(otherField, mark) as BaseOnlyFinalFactAp).access,
        )

        val treeRoot = assertNotNull(
            treeManager.mostAbstractFinalAp(base).concat(FactTypeChecker.Dummy, treeDelta),
        )
        val treeAfterField = assertNotNull(
            treeManager.abstractFinalOf(field).concat(FactTypeChecker.Dummy, treeDelta),
        )
        val baseOnlyResult = assertNotNull(
            baseOnlyManager.mostAbstractFinalAp(base).concat(FactTypeChecker.Dummy, baseOnlyDelta),
        )

        assertEquals(baseOnlyManager.finalOf(AnyAccessor, mark), baseOnlyResult)
        assertOverapproximates(
            listOf(treeRoot, treeAfterField),
            listOf(baseOnlyResult),
            "root suffix concat with implicit Any",
        )
    }

    @Test
    fun `contains and equalTo preserve every Tree-true relation`() {
        val (treeManager, baseOnlyManager) = managers()
        val treeFinal = treeManager.finalOf(field, mark)
        val baseOnlyFinal = baseOnlyManager.finalOf(field, mark)
        val treeExactInitial = treeManager.finalInitialOf(field, mark)
        val baseOnlyExactInitial = baseOnlyManager.finalInitialOf(field, mark)

        assertTrue(treeFinal.contains(treeExactInitial))
        assertTrue(baseOnlyFinal.contains(baseOnlyExactInitial), "BaseOnly lost Tree final containment")
        assertTrue(treeFinal.equalTo(treeExactInitial))
        assertTrue(baseOnlyFinal.equalTo(baseOnlyExactInitial), "BaseOnly lost Tree cross-kind equality")

        val treeAbstractFinal = treeManager.abstractFinalOf(field)
        val baseOnlyAbstractFinal = baseOnlyManager.abstractFinalOf(field)
        val treeAbstractInitial = treeManager.abstractInitialOf(field)
        val baseOnlyAbstractInitial = baseOnlyManager.abstractInitialOf(field)
        assertTrue(treeAbstractFinal.contains(treeAbstractInitial))
        assertTrue(baseOnlyAbstractFinal.contains(baseOnlyAbstractInitial))

        val treeExactInitialCopy = treeManager.finalInitialOf(field, mark)
        val baseOnlyExactInitialCopy = baseOnlyManager.finalInitialOf(field, mark)
        assertTrue(treeExactInitial.contains(treeExactInitialCopy))
        assertTrue(baseOnlyExactInitial.contains(baseOnlyExactInitialCopy))
        assertTrue(
            baseOnlyExactInitial.contains(baseOnlyExactInitialCopy.exclude(otherField)),
            "projected initial containment erases path-local exclusions conservatively",
        )
    }

    @Test
    fun `clear never removes a Tree-readable path`() {
        val (treeManager, baseOnlyManager) = managers()
        val tree = treeManager.finalOf(AnyAccessor, mark)
        val baseOnly = baseOnlyManager.finalOf(AnyAccessor, mark)

        for (accessor in listOf(field, otherField, ElementAccessor, mark)) {
            val treeCleared = tree.clearAccessor(accessor)
            val baseOnlyCleared = baseOnly.clearAccessor(accessor)
            if (treeCleared != null) {
                assertNotNull(baseOnlyCleared, "clear($accessor) removed a surviving Tree result")
                assertOverapproximates(listOf(treeCleared), listOf(baseOnlyCleared), "clear($accessor)")
            }
        }

        val treeExact = treeManager.finalOf(field, mark)
        val baseOnlyExact = baseOnlyManager.finalOf(field, mark)
        assertNull(treeExact.readAccessor(AnyAccessor))
        assertNull(
            baseOnlyExact.readAccessor(AnyAccessor),
            "an Any query must not consume an exact concrete-field edge",
        )
        val treeAfterAnyClear = assertNotNull(treeExact.clearAccessor(AnyAccessor))
        val baseOnlyAfterAnyClear = assertNotNull(
            baseOnlyExact.clearAccessor(AnyAccessor),
            "clearing an Any edge must not clear an exact concrete-field edge",
        )
        assertOverapproximates(listOf(treeAfterAnyClear), listOf(baseOnlyAfterAnyClear), "clear Any on exact field")
    }

    @Test
    fun `explicit Any projects to the implicit structural branch`() {
        for (fieldSensitive in listOf(false, true)) {
            val treeManager = TreeApManager(unrollStructural, RefManager(), Cancellation())
            val baseOnlyManager = BaseOnlyApManager(
                unrollStructural,
                Cancellation(),
                fieldSensitive = fieldSensitive,
            )
            val treeBare = treeManager.finalOf(mark)
            val baseOnlyBare = baseOnlyManager.finalOf(mark)

            assertNull(treeBare.clearAccessor(mark))
            assertEquals(baseOnlyBare, baseOnlyBare.clearAccessor(mark))
            assertEquals(baseOnlyBare, baseOnlyBare.clearAccessor(ValueAccessor))

            val treeAny = treeManager.finalOf(AnyAccessor, mark)
            val baseOnlyAny = baseOnlyManager.finalOf(AnyAccessor, mark) as BaseOnlyFinalFactAp
            assertEquals(NO_ACCESSOR, baseOnlyAny.access.fieldIdx)
            assertEquals(baseOnlyBare, baseOnlyAny)
            assertEquals(setOf(AnyAccessor, mark), baseOnlyAny.getStartAccessors())
            assertTrue(treeAny.startsWithAccessor(mark), "Tree Any child exposes its semantic suffix")
            assertTrue(baseOnlyAny.startsWithAccessor(mark), "BaseOnly Any must expose the same suffix")

            val treeAfterConcrete = assertNotNull(treeAny.readAccessor(field))
            val baseOnlyAfterConcrete = assertNotNull(baseOnlyAny.readAccessor(field))
            assertOverapproximates(
                listOf(treeAfterConcrete),
                listOf(baseOnlyAfterConcrete),
                "read concrete through Any",
            )
            assertNotNull(treeAny.clearAccessor(mark))
            assertNotNull(baseOnlyAny.clearAccessor(mark), "clear(mark) does not remove an Any root edge")
        }
    }

    @Test
    fun `fact and compatibility filters preserve all surviving Tree branches`() {
        val (treeManager, baseOnlyManager) = managers()
        val treeField = treeManager.finalOf(field, mark) as AccessTree
        val treeOther = treeManager.finalOf(otherField, mark) as AccessTree
        val treeMerged = AccessTree(
            treeManager,
            base,
            treeField.access.mergeAdd(treeOther.access),
            ExclusionSet.Empty,
        )
        val baseOnlyBranches = listOf(
            baseOnlyManager.finalOf(field, mark),
            baseOnlyManager.finalOf(otherField, mark),
        )

        val branchFilter = object : FactTypeChecker.FactApFilter {
            override fun check(accessor: Accessor): FactTypeChecker.FilterResult =
                if (accessor == otherField) FactTypeChecker.FilterResult.Reject
                else FactTypeChecker.FilterResult.Accept
        }
        val treeFiltered = listOfNotNull(treeMerged.filterFact(branchFilter))
        val baseOnlyFiltered = baseOnlyBranches.mapNotNull { it.filterFact(branchFilter) }
        assertTrue(treeFiltered.isNotEmpty())
        assertOverapproximates(treeFiltered, baseOnlyFiltered, "fact branch filter")

        val compatibilityFilter = object : FactTypeChecker.FactCompatibilityFilter {
            override fun check(accessor: Accessor): FactTypeChecker.CompatibilityFilterResult =
                if (accessor == otherField) FactTypeChecker.CompatibilityFilterResult.NotCompatible
                else FactTypeChecker.CompatibilityFilterResult.Compatible
        }
        val treeCompatible = listOfNotNull(treeMerged.filterFact(compatibilityFilter))
        val baseOnlyCompatible = baseOnlyBranches.mapNotNull { it.filterFact(compatibilityFilter) }
        assertTrue(treeCompatible.isNotEmpty())
        assertEquals(2, baseOnlyCompatible.size, "Tree compatibility filtering never checks wholly concrete paths")
        assertOverapproximates(treeCompatible, baseOnlyCompatible, "compatibility branch filter")

        val treeAbstractOther = treeManager.mostAbstractFinalAp(base).prependAccessor(otherField)
        val baseOnlyAbstractOther = baseOnlyManager.mostAbstractFinalAp(base).prependAccessor(otherField)
        assertNull(treeAbstractOther.filterFact(compatibilityFilter))
        assertNull(baseOnlyAbstractOther.filterFact(compatibilityFilter))

        val rejectOuterPrefix = object : FactTypeChecker.FactCompatibilityFilter {
            override fun check(accessor: Accessor): FactTypeChecker.CompatibilityFilterResult =
                if (accessor == stat) FactTypeChecker.CompatibilityFilterResult.NotCompatible
                else FactTypeChecker.CompatibilityFilterResult.Compatible
        }
        val treeNestedAbstract = treeManager.abstractFinalOf(stat, field)
        val baseOnlyNestedAbstract = baseOnlyManager.abstractFinalOf(stat, field)
        assertNotNull(treeNestedAbstract.filterFact(rejectOuterPrefix))
        assertNotNull(baseOnlyNestedAbstract.filterFact(rejectOuterPrefix))
    }

    @Test
    fun `abstractOnly then rebase never removes a Tree-readable path`() {
        val (treeManager, baseOnlyManager) = managers()
        val tree = treeManager.finalOf(AnyAccessor, mark)
        val baseOnly = baseOnlyManager.finalOf(AnyAccessor, mark)
        val treeAbstract = tree.abstractOnly()
        val baseOnlyAbstract = baseOnly.abstractOnly()
        assertOverapproximates(listOf(treeAbstract), listOf(baseOnlyAbstract), "abstractOnly")
        assertReadAndStartConformance(treeAbstract, baseOnlyAbstract, "abstractOnly")

        val newBase = AccessPathBase.Return
        val treeRebased = treeAbstract.rebase(newBase)
        val baseOnlyRebased = baseOnlyAbstract.rebase(newBase)
        assertEquals(newBase, treeRebased.base)
        assertEquals(newBase, baseOnlyRebased.base)
        assertOverapproximates(listOf(treeRebased), listOf(baseOnlyRebased), "abstract rebase")
    }

    @Test
    fun `serialization preserves each domain and BaseOnly still overapproximates Tree`() {
        val (treeManager, baseOnlyManager) = managers()
        val context = InMemoryContext()
        val treeSerializer = treeManager.createSerializer(context)
        val baseOnlySerializer = baseOnlyManager.createSerializer(context)
        val scenarios = listOf(
            listOf<Accessor>(stat, field, AnyAccessor, mark),
            listOf(TypeInfoGroupAccessor, typeInfo),
        )

        for (path in scenarios) {
            val tree = treeManager.finalOf(*path.toTypedArray())
            val baseOnly = baseOnlyManager.finalOf(*path.toTypedArray())
            val restoredTree = roundTripFinal(treeSerializer, tree)
            val restoredBaseOnly = roundTripFinal(baseOnlySerializer, baseOnly)

            assertEquals(tree, restoredTree, "Tree serialization changed $path")
            assertEquals(baseOnly, restoredBaseOnly, "BaseOnly serialization changed $path")
            assertOverapproximates(listOf(restoredTree), listOf(restoredBaseOnly), "serialization $path")
        }

        val treeInitial = treeManager.finalInitialOf(field, mark)
        val baseOnlyInitial = baseOnlyManager.finalInitialOf(field, mark)
        val restoredTreeInitial = roundTripInitial(treeSerializer, treeInitial)
        val restoredBaseOnlyInitial = roundTripInitial(baseOnlySerializer, baseOnlyInitial)
        assertEquals(treeInitial, restoredTreeInitial)
        assertEquals(baseOnlyInitial, restoredBaseOnlyInitial)
        assertOverapproximates(
            listOf(restoredTreeInitial),
            listOf(restoredBaseOnlyInitial),
            "initial serialization",
        )
    }

    private fun roundTripFinal(serializer: ApSerializer, fact: FinalFactAp): FinalFactAp {
        val bytes = ByteArrayOutputStream()
        DataOutputStream(bytes).use { output -> with(serializer) { output.writeFinalAp(fact) } }
        return DataInputStream(ByteArrayInputStream(bytes.toByteArray())).use { input ->
            with(serializer) { input.readFinalAp() }
        }
    }

    private fun roundTripInitial(serializer: ApSerializer, fact: InitialFactAp): InitialFactAp {
        val bytes = ByteArrayOutputStream()
        DataOutputStream(bytes).use { output -> with(serializer) { output.writeInitialAp(fact) } }
        return DataInputStream(ByteArrayInputStream(bytes.toByteArray())).use { input ->
            with(serializer) { input.readInitialAp() }
        }
    }

    private class InMemoryContext : SummarySerializationContext {
        private val accessorToId = HashMap<Accessor, Long>()
        private val idToAccessor = HashMap<Long, Accessor>()

        override fun getIdByAccessor(accessor: Accessor): Long =
            accessorToId.getOrPut(accessor) {
                accessorToId.size.toLong().also { idToAccessor[it] = accessor }
            }

        override fun getAccessorById(id: Long): Accessor = idToAccessor.getValue(id)
        override fun getIdByMethod(method: CommonMethod): Long = error("not used")
        override fun getMethodById(id: Long): CommonMethod = error("not used")
        override fun loadSummaries(method: CommonMethod): ByteArray? = error("not used")
        override fun storeSummaries(method: CommonMethod, summaries: ByteArray) = error("not used")
        override fun flush() = error("not used")
    }
}
