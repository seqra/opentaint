package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.Record
import org.opentaint.dataflow.bidi.store.AddedFactAccumulator
import kotlin.test.*

/** Production controls separate body growth, call-stage repeats, and boundary compression. */
class DemandRelativeWorkloadControlsTest {
    private fun summary(vararg edges: PathEdge): StatementSummary = StatementSummary(
        edges.flatMap { listOf(it.from.base,it.to.base) }.toSet(),edges.map(MicroEdge::of),emptyList(),emptyMap())

    @Test fun `shallow summary alternatives still join caller suffixes and callers`() {
        MethodAnalysisFixtures().use { f ->
            val p = AccessPathBase.Argument(0)
            val ret = AccessPathBase.Return
            val left = f.field("left"); val right = f.field("right")
            val a = f.field("a"); val b = f.field("b")
            val t = MarkSlot.Concrete(f.mark("T"))
            val premise = f.manager.initial(f.pattern(ret, tail = Tail.STAR, mark = MarkSlot.STAR))
            val summary = f.manager.mergeAddDelta(
                f.fact(p, listOf(left), Tail.STAR, MarkSlot.STAR),
                f.fact(p, listOf(right), Tail.STAR, MarkSlot.STAR)).first
            val paths = ArrayList<List<Int>>()
            repeat(3) {
                for (suffix in listOf(a, b)) {
                    val out = CollectingOut()
                    f.ops.applySummary(f.fact(ret, listOf(suffix), mark = t), premise, summary,
                        ApMode(false, Direction.BACKWARD, 3), out)
                    paths += out.results.flatMap { value -> f.ops.leaves(value).map { it.fact.path }.toList() }
                }
            }
            assertEquals(12, paths.size)
            assertEquals(setOf(listOf(left,a), listOf(left,b), listOf(right,a), listOf(right,b)), paths.toSet())
            println("SHALLOW_INTERPROC_JOIN summaryPaths=2 summaryMaxDepth=1 suffixes=2 callers=3 appliedPaths=${paths.size} resultMaxDepth=${paths.maxOf { it.size }}")
        }
    }

    @Test fun `reverse alias MAY images repeat equal shared suffix while output dedup has two rows`() {
        for (width in listOf(1,2,4,16,64)) MethodAnalysisFixtures().use { f ->
            val x=AccessPathBase.Argument(0)
            val alias=AccessPathBase.Argument(7)
            val t=MarkSlot.Concrete(f.mark("T"))
            val stages=arrayListOf<CallStage>(
                CallStage.Edges(BEFORE,BOUND,BIND_IN,summary(keepEdge(x),ZERO_KEEP)),
                CallStage.Actions(BOUND,ADDED,emptyList()),
                CallStage.Edges(ADDED,RETURNED,UNRESOLVED,summary(keepEdge(x),ZERO_KEEP)),
                CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,summary(keepEdge(x),ZERO_KEEP)),
                CallStage.Edges(REWRITTEN,AFTER,ALIASES,
                    summary(*(0 until width).map { starEdge(x,emptyList(),alias,listOf(f.field("f$it"))) }.toTypedArray()),Guard.MemoryEffect))
            f.call(1,CallPlan(setOf(x),stages,emptyList(),BEFORE,AFTER))
            lateinit var service:RunMethodCallServices
            val core=f.core(index=2,L=1,callFactory=MethodCallServicesFactory { RunMethodCallServices(it).also { s->service=s } })
            val initial=f.manager.initial(f.pattern(alias,tail=Tail.ANY,mark=t))
            service.process(EdgeDelta(initial,f.inst(1),f.fact(alias,tail=Tail.ANY,mark=t,layer=Layer.DEMAND)))
            val completed=f.cuts.filter { it.first==Cut.CALL }
            val xResults=completed.filter { it.second.base==x }
            val unique=xResults.map { it.second }.toSet()
            val stored=methodEntries(f.ops,core.edges.edgesAt(f.inst(1))).toList()
            println("ALIAS_BACKWARD width=$width callFinishes=${completed.size} xFinishes=${xResults.size} uniqueX=${unique.size} storedLeaves=${stored.size}")
            assertEquals(width,xResults.size)
            assertEquals(1,unique.size)
            assertEquals(width+1,completed.size)
            assertEquals(2,stored.size)
            assertTrue(xResults.all { it.second.layer==Layer.DEMAND })
        }
    }

    @Test fun `forward NORMAL identity bypasses the same alias fanout`() {
        for (width in listOf(1,2,4,16,64)) MethodAnalysisFixtures().use { f ->
            val x=AccessPathBase.Argument(0);val alias=AccessPathBase.Argument(7);val t=MarkSlot.Concrete(f.mark("T"))
            val plan=CallPlan(setOf(x),listOf(
                CallStage.Edges(BEFORE,BOUND,BIND_IN,summary(keepEdge(x))),
                CallStage.Actions(BOUND,ADDED,emptyList()),
                CallStage.Edges(ADDED,RETURNED,UNRESOLVED,summary(keepEdge(x))),
                CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,summary(keepEdge(x))),
                CallStage.Edges(REWRITTEN,AFTER,ALIASES,summary(*(0 until width).map {
                    starEdge(x,emptyList(),alias,listOf(f.field("f$it"))) }.toTypedArray()),Guard.MemoryEffect)),emptyList(),BEFORE,AFTER)
            f.call(1,plan)
            lateinit var service:RunMethodCallServices
            val core=f.core(index=3,L=2,callFactory=MethodCallServicesFactory { RunMethodCallServices(it).also { s->service=s } })
            val initial=f.manager.initial(f.pattern(x,mark=t))
            service.process(EdgeDelta(initial,f.inst(1),f.fact(x,mark=t)))
            val completed=f.cuts.filter { it.first==Cut.CALL }
            println("ALIAS_FORWARD width=$width callFinishes=${completed.size} storedLeaves=${methodEntries(f.ops,core.edges.edgesAt(f.inst(1))).count()}")
            assertEquals(1,completed.size)
            assertTrue(completed.all { it.second.base==x&&it.second.layer==Layer.NORMAL })
        }
    }

    /** These are explicit finite boundary obligations for the stated moves and
     * inverse reads. They do not inspect any production state or inferred row. */
    private fun inverseReadLoopDemand(f: MethodAnalysisFixtures, root: DemandPattern,
                                      p: AccessPathBase, x: AccessPathBase, ret: AccessPathBase,
                                      mark: MarkSlot, direction: Direction): DemandStore {
        val layout = f.contexts.blockLayout(f.key)
        val body = layout[layout.root]
        val before = checkNotNull(body.before)
        val loop = checkNotNull(body.loop)
        val after = checkNotNull(body.after)
        fun port(from: Int, to: Int) = checkNotNull(layout.port(from, to)).id
        val methodEntry = port(0, 1)
        val beforeLoop = port(1, 2)
        val leftRepeat = port(3, 2)
        val rightRepeat = port(4, 2)
        val afterLoop = port(2, 5)
        val methodExit = port(5, 6)
        fun may(base: AccessPathBase) = f.pattern(base, tail = Tail.ANY, mark = mark)
        val builder = DemandStore.Builder(f.manager).apply { add(f.key, root) }
        if (direction == Direction.BACKWARD) {
            builder.add(f.key, BlockScope(after, methodExit), afterLoop,
                DemandPattern(root.entry, may(x)))
            for (input in listOf(afterLoop, leftRepeat, rightRepeat))
                for (output in listOf(beforeLoop, leftRepeat, rightRepeat))
                    builder.add(f.key, BlockScope(loop, input), output, DemandPattern(may(x), may(x)))
            builder.add(f.key, BlockScope(before, beforeLoop), methodEntry, DemandPattern(may(x), may(p)))
        } else {
            builder.add(f.key, BlockScope(before, methodEntry), beforeLoop, DemandPattern(may(p), may(x)))
            for (input in listOf(beforeLoop, leftRepeat, rightRepeat))
                for (output in listOf(afterLoop, leftRepeat, rightRepeat))
                    builder.add(f.key, BlockScope(loop, input), output, DemandPattern(may(x), may(x)))
            builder.add(f.key, BlockScope(after, afterLoop), methodExit, DemandPattern(may(x), may(ret)))
        }
        return builder.build()
    }

    private fun requireInverseReadBody(f: MethodAnalysisFixtures, core: RunMethodAnalyzer) {
        val states = core.joinedBlockStates().filter { it.first != BlockScope.ROOT }
        assertTrue(states.isNotEmpty(), "This control must enter scoped analysis, not reject every local input")
        val layout = f.contexts.blockLayout(f.key)
        assertTrue(states.any { layout[it.first.block].isLoop && it.second.initials.admissions().isNotEmpty() },
            "The finite loop boundary obligations must admit actual loop initials")
        for (index in listOf(3, 4)) assertTrue(f.processed.any { it.node == f.inst(index) && it.facts !is Reach },
            "Both physical field reads must execute: missing $index")
    }

    @Test fun `scoped inverse read loop retains the flat demand image without its binary body workload`() {
        // Node walk(Node p) { Node x=p; while (choose()) { x=left()?x.left:x.right; } return x; }
        // The same root pair and actual as the flat control. Local pairs are now
        // explicit: a real preceding handoff supplies them in a driver sequence.
        for (limit in listOf(1,3,5,7)) MethodAnalysisFixtures(
            successors=listOf(listOf(1),listOf(2),listOf(3,4,5),listOf(2),listOf(2),listOf(6),emptyList()),
            normalExit=6).use { f ->
            val p=AccessPathBase.Argument(0);val x=AccessPathBase.LocalVar(0);val ret=AccessPathBase.Return
            val t=MarkSlot.Concrete(f.mark("T"));val left=f.field("left");val right=f.field("right")
            f.statement(1,MicroEdgeBuilder().apply { move(x,p) }.build())
            f.statement(3,MicroEdgeBuilder().apply { read(x,x,listOf(left)) }.build())
            f.statement(4,MicroEdgeBuilder().apply { read(x,x,listOf(right)) }.build())
            f.statement(5,MicroEdgeBuilder().apply { move(ret,x) }.build())
            val guide=DemandPattern(f.pattern(ret,mark=t),f.pattern(p,tail=Tail.ANY,mark=t))
            val demand=inverseReadLoopDemand(f,guide,p,x,ret,t,Direction.BACKWARD)
            val core=f.core(index=limit+1,L=limit,demand=demand)
            val admitted=demand.initials(f.key,f.fact(ret,tail=Tail.ANY,mark=t,layer=Layer.DEMAND),core.config.admissionPolicy)
            assertEquals(1,admitted.size)
            assertEquals(Layer.DEMAND,admitted.single().layer)
            admitted.forEach(core::addInitial)
            f.drain(core)
            requireInverseReadBody(f,core)
            val raw=core.summaries.all().flatMap { (_,facts)->f.ops.leaves(facts).map {
                Conclusion(it.fact,it.exclusion,facts.layer==Layer.DEMAND)
            } }.toSet()
            val selected=core.summaries.demandEdges(core.config.direction).flatMap { (_,facts)->f.ops.leaves(facts).map {
                Conclusion(it.fact,it.exclusion,facts.layer==Layer.DEMAND)
            } }.toSet()

            // Independent flat witness: each reversed read prepends left or
            // right. Every word has an executable choice of physical read 3/4.
            // Exact proper prefixes and MAY words at the global bound are the
            // old retained binary language, before the one-field exit cap.
            var words=setOf(emptyList<Int>())
            val flat=linkedSetOf<Conclusion>()
            repeat(limit) {
                for (word in words) flat += Conclusion(PathFact(p,word,Tail.EXACT,t),ExclusionSet.Empty,true)
                words=words.flatMap { word -> listOf(listOf(left)+word,listOf(right)+word) }.toSet()
            }
            for (word in words) flat += Conclusion(PathFact(p,word,Tail.ANY,t),ExclusionSet.Empty,true)
            assertEquals(1 shl limit,words.size)
            assertTrue(flat.size >= (1 shl limit), "The independent flat path-language witness is still exponential")
            val referenceCap=flat.map { org.opentaint.dataflow.bidi.ap.limit(it,1) }.toSet()
            val expected=referenceCap.filterTo(linkedSetOf()) { candidate ->
                referenceCap.none { it!=candidate && subsumes(it,candidate) }
            }
            assertEquals(setOf(
                Conclusion(f.pattern(p,mark=t).fact,ExclusionSet.Empty,true),
                Conclusion(f.pattern(p,listOf(left),Tail.ANY,t).fact,ExclusionSet.Empty,true),
                Conclusion(f.pattern(p,listOf(right),Tail.ANY,t).fact,ExclusionSet.Empty,true),
            ),expected)
            assertEquals(expected,selected,"The new body boundaries must retain the same selected flat union")
            assertEquals(selected,raw)

            val layout=f.contexts.blockLayout(f.key)
            val physical=core.joinedBlockStates().flatMap { (scope,state) ->
                val points=if(scope==BlockScope.ROOT) listOf(0,f.normalExit) else layout[scope.block].instructions
                points.flatMap { point -> state.edges.edgesAt(f.inst(point)).flatMap { (_,facts) ->
                    f.ops.leaves(facts).map { Conclusion(it.fact,it.exclusion,facts.layer==Layer.DEMAND) }
                }.toList() }
            }
            assertTrue(physical.isNotEmpty())
            assertTrue(physical.all { it.fact.path.size<=minOf(limit,2) },
                "A one-field scoped obligation needs at most the admitted prefix and one inverse read")
            if(limit==7) assertTrue(physical.size<flat.size,
                "The high-limit scoped body must remove work from the independent binary witness")
            println("FIELD_LOOP_BACKWARD limit=$limit processed=${core.steps} edgeDeltas=${core.edgeDeltas} admittedLeaves=${raw.size} selectedLeaves=${selected.size} pointLeaves=${physical.size} flatReferenceLeaves=${flat.size} bodyMaxDepth=${physical.maxOf { it.fact.path.size }} blocks=${core.blockDiagnostics()}")
        }
    }

    @Test fun `opposite native packed record is scalarized then repeats an equal call suffix`() {
        for (index in listOf(4,5)) for (protected in listOf(false,true)) MethodAnalysisFixtures().use { f ->
            val p=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
            val t=MarkSlot.Concrete(f.mark("T"));val u=f.mark("U")
            val a=f.field("a");val b=f.field("b");val h=f.field("h")
            // Code represented by the ordinary raw record: dup(p) { r.a=p;r.b=p;return r; }
            val nativePremise=f.manager.initial(f.pattern(p,tail=Tail.STAR,mark=MarkSlot.STAR))
            val nativeA=f.fact(ret,listOf(a),Tail.STAR,MarkSlot.STAR)
            val nativeB=f.fact(ret,listOf(b),Tail.STAR,MarkSlot.STAR)
            val native=f.manager.mergeAddDelta(nativeA,nativeB).first
            f.records.add(Record(f.key,Direction.FORWARD,nativePremise,native))
            val plan=CallPlan(setOf(p,ret),listOf(
                CallStage.Edges(BEFORE,BOUND,BIND_IN,summary(keepEdge(p),ZERO_KEEP)),
                CallStage.Actions(BOUND,ADDED,listOf(CleanStep.Clean(Cleaner(p,null,CleanReach.AT_AND_BELOW,u)))),
                CallStage.Callees(ADDED,RETURNED,listOf(f.key)),
                CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,summary(keepEdge(p),keepEdge(ret),ZERO_KEEP))),emptyList(),BEFORE,AFTER)
            f.call(1,plan)
            lateinit var service:RunMethodCallServices
            val core=f.core(index=index,L=index-1,callFactory=MethodCallServicesFactory { RunMethodCallServices(it).also { s->service=s } })
            val plain=if(index==4) f.manager.mergeAddDelta(
                f.fact(ret,listOf(a,h),Tail.ANY,t,layer=Layer.DEMAND),
                f.fact(ret,listOf(b,h),Tail.ANY,t,layer=Layer.DEMAND)).first
                else f.fact(p,listOf(h),mark=t)
            val actual=if (!protected) plain else (plain as TaintTree).withProtection(
                if(index==4) (f.fact(ret,listOf(a,h),Tail.ANY,t,layer=Layer.DEMAND) as TaintTree).root else plain.root)
            val origin=f.manager.initial(f.pattern(AccessPathBase.Argument(9),mark=t))
            val part=Subscription(f.key,CallerRef(f.key,origin,actual.layer,f.inst(1),stageOrdinal=2),actual.layer,actual)
            var nativeCallbacks=0;var reverseCallbacks=0
            val counting=object:SummaryApplier {
                override fun applySummary(part:Subscription,pub:Publication,member:Int)=error("No current summary")
                override fun applyRecord(part:Subscription,record:Record) { nativeCallbacks++;service.applyRecord(part,record) }
                override fun applyRecordView(part:Subscription,view:RecordLeafView,nonSubsumable:Boolean) {
                    reverseCallbacks++;service.applyRecordView(part,view,nonSubsumable)
                }
            }
            replayPersistedSummaries(core.config,f.ops,part,counting)
            val finishes=f.cuts.filter { it.first==Cut.CALL }
            val stored=methodEntries(f.ops,core.edges.edgesAt(f.inst(1))).toList()
            val retainedProtection=core.edges.edgesAt(f.inst(1)).any { (_,facts)->(facts as? TaintTree)?.nonSubsumable!=null }
            println("NATIVE_REPLAY run=$index protected=$protected nativeCallbacks=$nativeCallbacks reverseCallbacks=$reverseCallbacks callFinishes=${finishes.size} storedLeaves=${stored.size} retainedProtection=$retainedProtection")
            assertEquals(protected,retainedProtection)
            if(index==4) { assertEquals(2,reverseCallbacks);assertEquals(0,nativeCallbacks);assertEquals(2,finishes.size);assertEquals(1,stored.size) }
            else { assertEquals(0,reverseCallbacks);assertEquals(1,nativeCallbacks);assertEquals(1,finishes.size);assertEquals(2,stored.size) }
        }
    }

    @Test fun `forward uniform taint through the same binary read loop has a bounded broad image`() {
        for (limit in listOf(2,4,6)) MethodAnalysisFixtures(
            successors=listOf(listOf(1),listOf(2),listOf(3,4,5),listOf(2),listOf(2),listOf(6),emptyList()),
            normalExit=6).use { f ->
            val p=AccessPathBase.Argument(0);val x=AccessPathBase.LocalVar(0);val ret=AccessPathBase.Return
            val t=MarkSlot.Concrete(f.mark("T"));val left=f.field("left");val right=f.field("right")
            f.statement(1,MicroEdgeBuilder().apply { move(x,p) }.build())
            f.statement(3,MicroEdgeBuilder().apply { read(x,x,listOf(left)) }.build())
            f.statement(4,MicroEdgeBuilder().apply { read(x,x,listOf(right)) }.build())
            f.statement(5,MicroEdgeBuilder().apply { move(ret,x) }.build())
            val guide=DemandPattern(f.pattern(p,tail=Tail.ANY,mark=t),f.pattern(ret,tail=Tail.ANY,mark=t))
            val demand=inverseReadLoopDemand(f,guide,p,x,ret,t,Direction.FORWARD)
            val core=f.core(index=limit+1,L=limit,demand=demand)
            val admitted=demand.initials(f.key,f.fact(p,tail=Tail.ANY_TAINT,mark=t),core.config.admissionPolicy)
            assertEquals(1,admitted.size);assertEquals(Layer.NORMAL,admitted.single().layer)
            admitted.forEach(core::addInitial);f.drain(core)
            requireInverseReadBody(f,core)
            val raw=core.summaries.all().flatMap { (_,facts)->f.ops.leaves(facts) }.toList()
            println("FIELD_LOOP_FORWARD limit=$limit processed=${core.steps} edgeDeltas=${core.edgeDeltas} rawLeaves=${raw.size}")
            assertEquals(setOf(f.pattern(ret,tail=Tail.ANY_TAINT,mark=t)),raw.toSet(),
                "The admitted uniform taint must actually reach the public return")
            assertTrue(core.summaries.all().all { it.second.layer==Layer.NORMAL })
        }
    }

    @Test fun `exact caller input storage keeps covered descendants that have a different admission image`() {
        MethodAnalysisFixtures().use { f ->
            val ret=AccessPathBase.Return;val t=MarkSlot.Concrete(f.mark("T"));val field=f.field("f")
            val broad=f.fact(ret,tail=Tail.ANY,mark=t,layer=Layer.DEMAND)
            val child=f.fact(ret,listOf(field),Tail.ANY,t,layer=Layer.DEMAND)
            val origin=f.manager.initial(f.pattern(AccessPathBase.Argument(0),mark=t))
            val ref=CallerRef(f.key,origin,Layer.DEMAND,f.inst(1))
            val store=AddedFactAccumulator(f.manager)
            assertNotNull(store.add(ref,Layer.DEMAND,broad))
            val update=assertNotNull(store.add(ref,Layer.DEMAND,child))
            val current=store.snapshot(update.handle).facts
            val bp=f.ops.leaves(broad).single();val cp=f.ops.leaves(child).single()
            assertTrue(subsumes(Conclusion(bp.fact,bp.exclusion,true),Conclusion(cp.fact,cp.exclusion,true)))
            assertEquals(2,f.ops.leaves(current).count())
            val policy=RestrictedInitialPolicy(run=4,fieldLimit=3,direction=Direction.BACKWARD,catalog=f.manager.marks)
            val broadImage=assertNotNull(policy.emit(bp,bp))
            val childImage=assertNotNull(policy.emit(bp,cp))
            assertNotEquals(broadImage,childImage)
            println("CALLER_ANCESTOR_SUBSUMPTION broadCoversChild=true freshChild=true storedLeaves=${f.ops.leaves(current).count()} broadImage=${broadImage.fact.tail}:${broadImage.fact.path.size} childImage=${childImage.fact.tail}:${childImage.fact.path.size}")
        }
    }
}
