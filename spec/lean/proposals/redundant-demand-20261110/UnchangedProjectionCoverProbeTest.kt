package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.ZERO_FACT
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** Native correspondence for the proved finite-union law. No production retirement filter.
 * Inputs are legal admitted barrier rows, not a fabricated necessity example. */
class UnchangedProjectionCoverProbeTest {
    private data class Row(val method: MethodKey, val scope: BlockScope?, val port: PortId?,
                           val entry: DemandEntry, val exit: DemandExit)
    private data class Projection(val demand: DemandStore, val counts: Map<MethodKey, Int>)

    private fun privateField(value: Any, name: String): Any? =
        value.javaClass.getDeclaredField(name).also { it.isAccessible = true }.get(value)

    /** Inspect the actual frozen output. This is not a second projection implementation. */
    @Suppress("UNCHECKED_CAST")
    private fun snapshot(store: DemandStore): Set<Row> = buildSet {
        val public = privateField(store, "byMethod") as Map<MethodKey, Any>
        for ((method, index) in public) for (pair in privateField(index, "rows") as List<DemandPattern>)
            add(Row(method, null, null, DemandEntry.Data(pair.entry), DemandExit.Data(assertNotNull(pair.exit))))
        for ((method, rows) in privateField(store, "controls") as Map<MethodKey, List<PairedDemand>>)
            for (pair in rows) add(Row(method, null, null, pair.entry, pair.exit))
        for ((owner, index) in privateField(store, "scoped") as Map<OwnedScope, Any>) {
            val rows = privateField(privateField(index, "data")!!, "rows") as List<DemandPattern>
            val ports = privateField(index, "rowPorts") as List<PortId>
            for ((i, pair) in rows.withIndex())
                add(Row(owner.method, owner.local, ports[i], DemandEntry.Data(pair.entry),
                    DemandExit.Data(assertNotNull(pair.exit))))
            for ((port, pair) in privateField(index, "controls") as List<Pair<PortId, PairedDemand>>)
                add(Row(owner.method, owner.local, port, pair.entry, pair.exit))
        }
    }

    private fun config(f: MethodAnalysisFixtures, run: Int, demand: DemandStore = DemandStore.Builder(f.manager).build()) =
        RunConfig(run, maxOf(1, run - 1), demand, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)

    private fun methods(f: MethodAnalysisFixtures, run: Int,
                        rows: List<Pair<PremiseKey, Facts>>, targets: List<TargetSummary> = emptyList(),
                        sinkSeed: Seed? = null, source: PathEdge? = null): Pair<HandOff, RunMethodAnalyzer> {
        val demand = DemandStore.Builder(f.manager).apply {
            // Actual emitTarget admission uses a complete existing typed pair.
            add(f.key, PairedDemand(DemandEntry.Target, DemandExit.Zero))
            for (row in targets) for (member in row.premise.members) if (!member.isZero)
                add(f.key, PairedDemand(DemandEntry.Data(member.toPattern()), DemandExit.Zero))
        }.build()
        val c = config(f, run, demand)
        val actor = f.core(c)
        for ((premise, facts) in rows) actor.summaries.addAdmittedAll(premise, facts)
        for (row in targets) actor.emitTarget(row.premise, row.target)
        sinkSeed?.let(actor.sinkSeeds::add)
        source?.let { assertNotNull(actor.sourceHits).add(f.key, f.inst(0), it) }
        f.drain(actor); actor.freeze()
        val result = RunResult(RunStatus.COMPLETE, listOf(actor), run, c.direction, MarkMode.FULL)
        return HandOff.of(c, result, f.shared) to actor
    }

    private fun blocks(f: MethodAnalysisFixtures, direction: Direction,
                       summaries: List<ScopedRunSummary>, targets: List<ScopedTargetRows> = emptyList()): Projection {
        val builder = DemandStore.Builder(f.manager)
        val counts = LinkedHashMap<MethodKey, Int>()
        projectBlockHandOff(f.manager, direction, false, summaries.asSequence(), targets.asSequence(), builder, counts)
        return Projection(builder.build(), counts)
    }

    private fun store(f: MethodAnalysisFixtures, rows: List<Pair<PremiseKey, Facts>>) =
        RunSummaryStore(f.manager, flowBacked = true).apply { rows.forEach { (p, c) -> addAdmittedAll(p, c) } }

    private fun raw(f: MethodAnalysisFixtures, p: Pattern, layer: Layer = Layer.DEMAND, protected: Boolean = false): Facts {
        val facts = f.manager.factsOf(p.fact, p.exclusion, layer)
        return if (protected) (facts as TaintTree).withProtection(facts.root) else facts
    }

    private fun checkQueries(f: MethodAnalysisFixtures, baseline: DemandStore, filtered: DemandStore,
                             incoming: Pattern, outgoing: Pattern, run: Int, scoped: ScopedSummaryKey? = null) {
        val direction = if (run % 2 == 1) Direction.FORWARD else Direction.BACKWARD
        val policy = RestrictedInitialPolicy(run, run - 1, direction, f.manager.marks)
        val a = scoped?.let { baseline.scope(f.key, it.scope) }
        val b = scoped?.let { filtered.scope(f.key, it.scope) }
        var admitted = 0
        var intersected = 0
        for (tail in listOf(Tail.EXACT, Tail.ANY, Tail.ANY_TAINT, Tail.STAR)) {
            val offered = raw(f, incoming.copy(fact = incoming.fact.copy(tail = tail)),
                if (tail == Tail.ANY || tail == Tail.STAR) Layer.DEMAND else Layer.NORMAL)
            val ai = a?.initials(offered, policy) ?: baseline.initials(f.key, offered, policy)
            val bi = b?.initials(offered, policy) ?: filtered.initials(f.key, offered, policy)
            assertEquals(ai, bi, "C2: $tail")
            admitted += ai.size
            for (initial in ai) for (protected in listOf(false, true)) for (outputTail in listOf(Tail.EXACT,Tail.STAR,Tail.ANY)) {
                val output = raw(f, outgoing.copy(fact=outgoing.fact.copy(tail=outputTail)), protected = protected)
                val ac = a?.intersect(scoped!!.exit, initial.initial, output, policy)
                    ?: baseline.intersect(f.key, initial.initial, output, policy)
                val bc = b?.intersect(scoped!!.exit, initial.initial, output, policy)
                    ?: filtered.intersect(f.key, initial.initial, output, policy)
                assertEquals(ac.toSet(), bc.toSet(), "C5: $tail protected=$protected")
                intersected += ac.size
            }
        }
        assertTrue(admitted>0,"At least one positive C2 cell must execute")
        assertTrue(intersected>0,"At least one positive C5 cell must execute")
        val wrong = incoming.copy(fact = incoming.fact.copy(mark = MarkSlot.Concrete(f.mark("U"))))
        val offered = raw(f, wrong)
        assertEquals(a?.initials(offered, policy) ?: baseline.initials(f.key, offered, policy),
            b?.initials(offered, policy) ?: filtered.initials(f.key, offered, policy))
    }

    @Test fun `actual protected MAY debt and protected MUST anchor have equal native method and block guidance`() {
        MethodAnalysisFixtures().use { f ->
            // Full mark T is an injective renaming of the captured concrete Spring mark.
            val mark = MarkSlot.Concrete(f.mark("T"))
            val mapKey = f.field("MapKey")
            val p = f.manager.initial(f.pattern(AccessPathBase.Argument(0), listOf(mapKey), Tail.STAR, mark))
            val may = f.pattern(AccessPathBase.Return, tail = Tail.ANY, mark = mark)
            val x = p to raw(f, may, protected = true)
            val y = p to raw(f, may.copy(fact = may.fact.copy(tail = Tail.ANY_TAINT)), protected = true)
            assertEquals(2, store(f, listOf(x, y)).all().count(), "Do not store-subsume or rewrite either current row")
            for (run in listOf(7, 8)) {
                val (before, actor) = methods(f, run, listOf(x, y))
                val (after, retained) = methods(f, run, listOf(y))
                assertEquals(snapshot(before.demand), snapshot(after.demand))
                assertEquals(before.demandEdges, after.demandEdges)
                assertEquals(mapOf(f.key to 1), before.demandEdges)
                assertEquals(2, actor.summaries.all().count())
                assertEquals(1, retained.summaries.all().count())
                assertFalse(before.demand.hasStaticCompletion || after.demand.hasSharedStaticCarry)
                checkQueries(f, before.demand, after.demand, may, p.toPattern(), run + 1)

                val key = ScopedSummaryKey(f.key, BlockScope(BlockId(1), PortId(3)), PortId(7))
                val direction = if (run == 7) Direction.FORWARD else Direction.BACKWARD
                val b = blocks(f, direction, listOf(ScopedRunSummary(key, store(f, listOf(x,y)))))
                val c = blocks(f, direction, listOf(ScopedRunSummary(key, store(f, listOf(y)))))
                assertEquals(snapshot(b.demand), snapshot(c.demand))
                assertEquals(b.counts, c.counts)
                assertEquals(setOf(key.reversed().scope), snapshot(b.demand).map { it.scope }.toSet())
                checkQueries(f, b.demand, c.demand, may, p.toPattern(), run + 1, key.reversed())
                val wrongPort = key.copy(exit = PortId(8))
                val mismatch = blocks(f, direction, listOf(ScopedRunSummary(wrongPort, store(f, listOf(y)))))
                assertNotEquals(snapshot(b.demand), snapshot(mismatch.demand), "A different exit cannot anchor this projection")
            }
        }
    }

    @Test fun `plain and protected flag memberships remain distinct while native projection forgets the flag`() {
        MethodAnalysisFixtures().use { f ->
            val p = f.manager.initial(f.pattern(AccessPathBase.Argument(0), tail = Tail.STAR))
            val output = f.pattern(AccessPathBase.Return, tail = Tail.ANY)
            val plain = p to raw(f, output)
            val protected = p to raw(f, output, protected = true)
            val both = methods(f, 7, listOf(plain, protected))
            val anchor = methods(f, 7, listOf(plain))
            assertEquals(2, both.second.summaries.all().count())
            assertEquals(snapshot(both.first.demand), snapshot(anchor.first.demand))
            assertTrue(snapshot(methods(f, 7, emptyList()).first.demand).isEmpty(),
                "If both rows are in U, deleting both loses their projection; they cannot anchor one another")
        }
    }

    @Test fun `native ND projection needs every arm and normal ND remains selected`() {
        MethodAnalysisFixtures().use { f ->
            val a = f.manager.initial(f.pattern(AccessPathBase.Argument(0)))
            val b = f.manager.initial(f.pattern(AccessPathBase.Argument(1)))
            val nd = f.manager.union(a,b)
            val output = f.pattern(AccessPathBase.Return, tail = Tail.ANY)
            val x = nd to raw(f, output)
            val anchors = listOf(a to raw(f, output), b to raw(f, output))
            val baseline = methods(f, 7, listOf(x)+anchors).first
            val filtered = methods(f, 7, anchors).first
            assertEquals(snapshot(baseline.demand), snapshot(filtered.demand))
            assertEquals(2, snapshot(filtered.demand).size)
            assertNotEquals(snapshot(filtered.demand), snapshot(methods(f, 7, anchors.take(1)).first.demand),
                "A single anchor covers only one ND projection")
            val normal = nd to raw(f, output.copy(fact=output.fact.copy(tail=Tail.ANY_TAINT)), Layer.NORMAL)
            val normalGuidance = methods(f, 7, listOf(normal)).first
            assertEquals(snapshot(filtered.demand), snapshot(normalGuidance.demand))
            val key = ScopedSummaryKey(f.key, BlockScope(BlockId(2),PortId(4)),PortId(9))
            val block = blocks(f, Direction.FORWARD, listOf(ScopedRunSummary(key,store(f,listOf(x)+anchors))))
            val keep = blocks(f, Direction.FORWARD, listOf(ScopedRunSummary(key,store(f,anchors))))
            assertEquals(snapshot(block.demand),snapshot(keep.demand))
            assertEquals(2, snapshot(block.demand).size)
        }
    }

    @Test fun `actual guidance normalization clears abstract exclusions and normalizes MUST`() {
        MethodAnalysisFixtures().use { f ->
            val field = f.field("excluded")
            val a = f.manager.initial(f.pattern(AccessPathBase.Argument(0),tail=Tail.STAR,mark=MarkSlot.STAR))
            val base = f.pattern(AccessPathBase.Return,tail=Tail.STAR,mark=MarkSlot.STAR)
            val plain = a to raw(f,base)
            val withExclusion = a to f.manager.flowTree(AccessPathBase.Return,Layer.DEMAND,
                ExclusionSet.of(field),MarkExclusions.fromMarks(MarkSet.of(f.mark("U"))),
                (raw(f,base) as FlowTree).root,Tail.STAR)
            assertEquals(snapshot(methods(f,7,listOf(plain,withExclusion)).first.demand),
                snapshot(methods(f,7,listOf(plain)).first.demand))
        }
    }

    @Test fun `typed ZERO and Target guidance and independent seeds stay unchanged`() {
        MethodAnalysisFixtures().use { f ->
            val a = f.manager.initial(f.pattern(AccessPathBase.Argument(0)))
            val b = f.manager.initial(f.pattern(AccessPathBase.Argument(1)))
            val nd = f.manager.union(a,b)
            val targets = listOf(TargetSummary(nd,Target.DemandTarget),
                TargetSummary(a,Target.DemandTarget),TargetSummary(b,Target.DemandTarget))
            val all = methods(f,7,emptyList(),targets).first
            val keep = methods(f,7,emptyList(),targets.drop(1)).first
            assertEquals(snapshot(all.demand),snapshot(keep.demand))
            assertEquals(2,snapshot(keep.demand).size)
            assertTrue(snapshot(keep.demand).all { it.entry==DemandEntry.Target && it.exit is DemandExit.Data })
            val key = ScopedSummaryKey(f.key,BlockScope(BlockId(3),PortId(5)),PortId.ROOT_EXIT)
            val blockAll = blocks(f,Direction.FORWARD,emptyList(),listOf(ScopedTargetRows(f.key,key.scope,targets,key.exit)))
            val blockKeep = blocks(f,Direction.FORWARD,emptyList(),listOf(ScopedTargetRows(f.key,key.scope,targets.drop(1),key.exit)))
            assertEquals(snapshot(blockAll.demand),snapshot(blockKeep.demand))
            assertTrue(snapshot(blockKeep.demand).all { it.scope==key.reversed().scope && it.port==key.scope.entry })
            val out = f.pattern(AccessPathBase.Return,tail=Tail.ANY)
            val x = f.manager.zero to raw(f,out,protected=true)
            val y = f.manager.zero to raw(f,out.copy(fact=out.fact.copy(tail=Tail.ANY_TAINT)),protected=true)
            val z = methods(f,7,listOf(x,y)).first
            val zKeep = methods(f,7,listOf(y)).first
            assertEquals(snapshot(z.demand),snapshot(zKeep.demand))
            assertTrue(snapshot(zKeep.demand).single().exit==DemandExit.Zero)

            val source = PathEdge(ZERO_FACT,f.pattern(AccessPathBase.Return).fact,ExclusionSet.Empty)
            val backwardAll = methods(f,8,listOf(x,y),source=source).first
            val backwardKeep = methods(f,8,listOf(y),source=source).first
            assertEquals(snapshot(backwardAll.demand),snapshot(backwardKeep.demand))
            assertEquals(1,backwardAll.seeds.size)
            assertEquals(backwardAll.seeds.at(f.key,f.inst(0)),backwardKeep.seeds.at(f.key,f.inst(0)))
            assertTrue(backwardKeep.seeds.allowsSource(f.key,f.inst(0),source))
            val sink = Seed.PredicateSink(org.opentaint.dataflow.bidi.interp.RuleOccurrenceId(
                org.opentaint.dataflow.bidi.interp.FormKey(org.opentaint.dataflow.bidi.interp.FormOwner(),
                    f.key.method,f.key,f.inst(1)),org.opentaint.dataflow.bidi.interp.RuleKind.CALL_SINK,0),f.key,f.inst(1))
            val forwardAll = methods(f,7,listOf(x,y),sinkSeed=sink).first
            val forwardKeep = methods(f,7,listOf(y),sinkSeed=sink).first
            assertEquals(forwardAll.seeds.at(f.key,f.inst(1)),forwardKeep.seeds.at(f.key,f.inst(1)))
            assertEquals(1,forwardKeep.seeds.size)
        }
    }
}
