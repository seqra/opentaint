package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.bidi.store.reference.ReferenceFrozenStaticCompletion
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class PackedStaticGuidanceTest {
    private class Fixture {
        val f = EngineShellFixtures(markDeclarations = testDeclarations(
            TestMark("T", MarkGroupKey.Rule("shared")), TestMark("U", MarkGroupKey.Rule("shared")), TestMark("V")))
        val ap = f.manager
        val cls = ap.accessors.index(ClassStaticAccessor("C"))
        val field = f.field("field")
        val child = f.field("child")
        val t = MarkSlot.Concrete(ap.marks.mark("T"))
        val u = MarkSlot.Concrete(ap.marks.mark("U"))
        val v = MarkSlot.Concrete(ap.marks.mark("V"))
        val group = MarkSlot.Concrete(ap.marks.group(ap.marks.groupOf(t.mark)))
        val colors = listOf(MarkSlot.STAR, t, u, v, group)
        val owner = ScopedSummaryKey(f.a, BlockScope(BlockId(3), PortId(10)), PortId(20))
        val second = owner.copy(scope = owner.scope.copy(entry = PortId(11)))
        val empty = owner.copy(exit = PortId.STATIC_SHORTCUT)
        val graph = DetachedStaticCallGraph.copyOf(mapOf(f.a.method to setOf(f.b.method)), f.cancellation)
        fun c(index: Int = 0, mark: MarkSlot = MarkSlot.STAR, tail: Tail = Tail.STAR,
              e: ExclusionSet = ExclusionSet.Empty) = Pattern(PathFact(STATIC,
            listOf(cls, field) + List(index) { child }, tail, mark), e)
        fun p(base: AccessPathBase, mark: MarkSlot = MarkSlot.STAR, path: List<Int> = emptyList(),
              tail: Tail = Tail.STAR, e: ExclusionSet = ExclusionSet.Empty) = Pattern(PathFact(base,path,tail,mark),e)
        val x get() = p(AccessPathBase.Argument(0))
        val y get() = p(AccessPathBase.Return)
        val samples get() = colors.flatMap { mark -> listOf(c(mark=mark), c(1,mark),
            p(AccessPathBase.Argument(0),mark),p(AccessPathBase.Return,mark),p(AccessPathBase.Return,mark,listOf(child))) } + ap.zero.toPattern()
        fun seeds(add: (MethodKey, Pattern, Pattern) -> Unit, scoped: (ScopedSummaryKey,Pattern,Pattern)->Unit,
                  target: (MethodKey,Pattern)->Unit, scopedTarget: (ScopedSummaryKey,Pattern)->Unit,
                  entered: (ScopedSummaryKey)->Unit) {
            // Global geometry order differs from this owner's first geometry order.
            add(f.b,c(1,t),p(AccessPathBase.Return,t))
            for (mark in colors) {
                add(f.a,p(AccessPathBase.Argument(0),mark),c(mark=mark))
                add(f.a,c(mark=mark),c(1,mark))
                add(f.a,c(1,mark),p(AccessPathBase.Return,mark))
                scoped(owner,p(AccessPathBase.Argument(0),mark),c(mark=mark))
                scoped(owner,c(1,mark),p(AccessPathBase.Return,mark))
            }
            add(f.a,p(AccessPathBase.Argument(0),t),c(mark=u))
            add(f.a,p(AccessPathBase.Argument(0),u),c(mark=v))
            add(f.a,ap.zero.toPattern(),c(mark=t))
            add(f.a,c(mark=u),ap.zero.toPattern())
            val excluded = ExclusionSet.of(intArrayOf(child))
            add(f.a,p(AccessPathBase.Argument(0),t,e=excluded),c(mark=u,e=excluded))
            add(f.a,p(AccessPathBase.Argument(0),t,tail=Tail.ANY_TAINT,e=excluded),c(mark=u,tail=Tail.ANY_TAINT,e=excluded))
            add(f.a,p(AccessPathBase.Argument(0),t),c(mark=u)) // exact duplicate
            scoped(second,p(AccessPathBase.Argument(0),v),c(1,v))
            entered(empty)
            target(f.a,c(mark=t)); target(f.a,c(mark=u)); target(f.a,c(mark=t))
            scopedTarget(owner,c(mark=u)); scopedTarget(second,c(1,v))
        }
        fun snapshots(): Pair<FrozenStaticCompletion,ReferenceFrozenStaticCompletion> {
            val packed=FrozenStaticCompletion.Builder(ap,graph)
            val reference=ReferenceFrozenStaticCompletion.Builder(ap,graph)
            seeds(packed::addSeed,packed::addScopedSeed,packed::addTarget,packed::addScopedTarget,packed::addScopedBoundary)
            seeds(reference::addSeed,reference::addScopedSeed,reference::addTarget,reference::addScopedTarget,reference::addScopedBoundary)
            return packed.build() to reference.build()
        }
    }

    @Test fun `endpoint word round trips real ZERO and maximum mark IDs without conflating FLOW`() {
        val marks = listOf(TaintMark.ZERO,TaintMark(1),TaintMark(Int.MAX_VALUE))
        for (input in marks) for (output in marks) {
            val a=MarkSlot.Concrete(input); val b=MarkSlot.Concrete(output)
            val label=BoundaryMarkCodec.pack(a,b)
            assertNotEquals(0L,label)
            assertEquals(a,BoundaryMarkCodec.input(label))
            assertEquals(b,BoundaryMarkCodec.output(label))
        }
        assertEquals(0L,BoundaryMarkCodec.pack(MarkSlot.STAR,MarkSlot.STAR))
        assertFailsWith<IllegalStateException> { BoundaryMarkCodec.pack(MarkSlot.STAR,MarkSlot.Concrete(TaintMark(1))) }
        val f=Fixture()
        val zero=f.ap.zero.toPattern()
        val colored=f.c(mark=f.t)
        val geometry=GuidanceGeometry(zero.copy(fact=zero.fact.copy(mark=MarkSlot.STAR)),
            colored.copy(fact=colored.fact.copy(mark=MarkSlot.STAR)))
        assertEquals(GuidanceMarks.Mapped(null,f.t.mark),BoundaryMarkCodec.relation(geometry,
            BoundaryMarkCodec.pack(zero.fact.mark,colored.fact.mark)))
    }

    @Test fun `packed normalized metadata keeps concrete E and separate exact paired labels`() {
        val f=Fixture(); val pool=PackedGuidanceCatalog.Builder(); val rows=PackedGuidanceRows.Builder(pool)
        val e=ExclusionSet.of(f.child)
        val inputs=listOf(f.t to f.u,f.u to f.v,f.group to f.t)
        val originals=inputs.map { (from,to) ->
            f.p(AccessPathBase.Argument(0),from,e=e) to f.c(mark=to,e=e)
        }
        for ((a,b) in originals) rows.add(a,b)
        val normalized=originals.map { (a,b) -> StaticGuidanceEdge.of(a,b) }
        val catalog=pool.freeze(); val packed=rows.freeze(catalog)
        assertEquals(1,catalog.geometryCount)
        assertEquals(normalized,(0 until packed.size).map(packed::edge))
        assertEquals(e,packed.to(0).exclusion,"Installing the abstract metadata mark must not normalize concrete E again")
        assertFalse((0 until packed.size).map(packed::marks).contains(GuidanceMarks.Mapped(f.t.mark,f.v.mark)))
    }

    @Test fun `finite codec adapter agrees with native normalization for FLOW mx MUST E and class markers`() {
        val f=Fixture(); val pool=PackedGuidanceCatalog.Builder(); val rows=PackedGuidanceRows.Builder(pool)
        val expected=LinkedHashSet<StaticGuidanceEdge>()
        val excluded=ExclusionSet.of(f.child)
        val flowA=MarkSlot.Star(MarkSet.of(f.t.mark)); val flowB=MarkSlot.Star(MarkSet.of(f.u.mark))
        for((input,output) in listOf(flowA to flowB,f.t to f.u,f.u to f.group))
            for(tail in Tail.entries) for(e in listOf(ExclusionSet.Empty,excluded)) {
                val local=f.p(AccessPathBase.Argument(0),input,tail=tail,e=e)
                val static=f.c(mark=output,tail=tail,e=e)
                for((a,b) in listOf(local to static,static to local)) {
                    rows.add(a,b); expected+=StaticGuidanceEdge.of(a,b)
                }
            }
        val marker=Pattern(PathFact(STATIC,listOf(f.cls),Tail.EXACT,f.t),ExclusionSet.Empty)
        rows.add(marker,f.p(AccessPathBase.Return,f.u,tail=Tail.EXACT))
        expected+=StaticGuidanceEdge.of(marker,f.p(AccessPathBase.Return,f.u,tail=Tail.EXACT))
        val packed=rows.freeze(pool.freeze())
        assertEquals(expected.toList(),(0 until packed.size).map(packed::edge))
    }

    @Test fun `frozen catalog stays detached while builder can make later snapshots without duplicate rows`() {
        val f=Fixture(); val packed=FrozenStaticCompletion.Builder(f.ap,f.graph)
        val reference=ReferenceFrozenStaticCompletion.Builder(f.ap,f.graph)
        packed.addSeed(f.f.a,f.x,f.c()); reference.addSeed(f.f.a,f.x,f.c())
        packed.addTarget(f.f.a,f.c(mark=f.t)); reference.addTarget(f.f.a,f.c(mark=f.t))
        val first=packed.build(); val expectedFirst=reference.build()
        packed.addSeed(f.f.a,f.x,f.c()); reference.addSeed(f.f.a,f.x,f.c())
        packed.addSeed(f.f.a,f.c(),f.y); reference.addSeed(f.f.a,f.c(),f.y)
        packed.addTarget(f.f.a,f.c(mark=f.t)); reference.addTarget(f.f.a,f.c(mark=f.t))
        val second=packed.build(); val expectedSecond=reference.build()
        assertEquals(expectedFirst.local(f.f.a).targets(f.c()).toList(),first.local(f.f.a).targets(f.c()).toList())
        assertEquals(expectedFirst.local(f.f.a).targetInputs().toList(),first.local(f.f.a).targetInputs().toList())
        assertEquals(expectedSecond.local(f.f.a).targets(f.y).toList(),second.local(f.f.a).targets(f.y).toList())
        assertEquals(1L,second.writerAttachments)
        assertEquals(1L,second.readerAttachments)
        assertEquals(expectedSecond.local(f.f.a).targetInputs().toList(),second.local(f.f.a).targetInputs().toList())
    }

    @Test fun `freeze drops populated builder index owners including their backing capacity`() {
        val f=Fixture(); val pool=PackedGuidanceCatalog.Builder()
        val rows=PackedGuidanceRows.Builder(pool); val endpoints=PackedEndpointRows.Builder(pool)
        rows.add(f.x,f.c()); endpoints.add(f.c(mark=f.t))
        fun field(owner:Any,name:String):Any = owner.javaClass.getDeclaredField(name)
            .apply { isAccessible=true }.get(owner)
        val oldEndpointIndex=field(pool,"endpointIds")
        val oldGeometryIndex=field(pool,"geometryIds")
        val oldRowsIndex=field(rows,"seen")
        val oldEndpointsIndex=field(endpoints,"seen")
        val projected=field(rows,"projected")
        val oldProjectedIndex=field(projected,"seen")
        assertTrue((oldEndpointIndex as Map<*,*>).isNotEmpty())
        assertTrue((oldGeometryIndex as Map<*,*>).isNotEmpty())
        assertTrue((oldRowsIndex as Map<*,*>).isNotEmpty())
        val catalog=pool.freeze()
        val frozenRows=rows.freeze(catalog); rows.freezeEntries(catalog); endpoints.freeze(catalog)
        for((owner,name,old) in listOf(Triple(pool,"endpointIds",oldEndpointIndex),
            Triple(pool,"geometryIds",oldGeometryIndex),Triple(rows,"seen",oldRowsIndex),
            Triple(endpoints,"seen",oldEndpointsIndex),Triple(projected,"seen",oldProjectedIndex))) {
            assertNotSame(old,field(owner,name),"$name must replace its owning container, not only clear entries")
            assertTrue((field(owner,name) as Map<*,*>).isEmpty())
        }
        assertEquals(listOf(StaticGuidanceEdge.of(f.x,f.c())),(0 until frozenRows.size).map(frozenRows::edge))
    }

    @Test fun `frozen boundary and terminal storage has no rich row backing`() {
        val f=Fixture(); val (packed,_)=f.snapshots()
        for (name in listOf("locals","scopedLocals")) {
            val field=packed.javaClass.getDeclaredField(name).apply { isAccessible=true }
            for (attachment in (field.get(packed) as Map<*,*>).values) {
                assertNotNull(attachment)
                for (rowsName in listOf("writerRows","readerRows")) {
                    val rows=attachment.javaClass.getDeclaredField(rowsName).apply { isAccessible=true }.get(attachment)
                    assertFalse(rows is List<*>, "Frozen $rowsName must retain primitive memberships, not rich rows")
                }
            }
        }
        val terminals=packed.javaClass.getDeclaredField("terminalReaders").apply { isAccessible=true }.get(packed) as Map<*,*>
        assertTrue(terminals.values.none { it is List<*> }, "Terminal inputs must use typed primitive memberships")
    }

    @Test fun `owner geometry groups keep their first occurrence rather than pool order`() {
        val f=Fixture()
        val a=StaticGuidanceEdge.of(f.c(mark=f.t),f.p(AccessPathBase.Return,f.t))
        val b=StaticGuidanceEdge.of(f.c(1,f.t),f.p(AccessPathBase.Return,f.t))
        val snapshot=FrozenStaticCompletion.Builder(f.ap,f.graph).apply {
            addSeed(f.f.b,a)
            addSeed(f.f.a,b)
            addSeed(f.f.a,a)
        }.build()
        assertEquals(listOf(b,a),snapshot.local(f.f.a).targets(f.y).toList())
    }

    @Test fun `terminal inputs stay distinct from real ZERO writer slots and empty entered ports`() {
        val f=Fixture(); val zero=f.ap.zero.toPattern()
        val snapshot=FrozenStaticCompletion.Builder(f.ap,f.graph).apply {
            addSeed(f.f.a,zero,f.c(mark=f.t))
            addTarget(f.f.a,f.c(mark=f.t))
            addTarget(f.f.a,zero)
            addTarget(f.f.a,f.p(AccessPathBase.Return,f.t))
            addScopedTarget(f.empty,zero) // Registration precedes anchor rejection.
        }.build()
        val view=snapshot.local(f.f.a)
        assertEquals(listOf(f.c(mark=f.t)),view.targetInputs().toList())
        assertEquals(listOf(StaticGuidanceEdge.of(zero,f.c(mark=f.t))),view.incoming(f.c(mark=f.t)).toList())
        assertTrue(view.targets(zero).none(),"A terminal must not turn into static-to-ZERO data")
        val scoped=snapshot.scopedViews().single()
        assertEquals(OwnedScope(f.empty.method,f.empty.reversed().scope),scoped.first)
        assertTrue(scoped.second.local(f.f.a).targetInputs().none())
    }

    @Test fun `frozen packed graph cannot retain rich edges or actor service owners`() {
        val f=Fixture(); val (snapshot,_)=f.snapshots()
        val seen=java.util.IdentityHashMap<Any,Boolean>()
        val pending=java.util.ArrayDeque<Any>().apply { add(snapshot) }
        while(pending.isNotEmpty()) {
            val value=pending.removeFirst()
            if(seen.put(value,true)!=null) continue
            assertFalse(value is StaticGuidanceEdge,"A frozen catalog retains geometry and label words only")
            val type=value.javaClass
            assertFalse(type.name.startsWith("org.opentaint.dataflow.bidi.engine."),"Live engine owner retained: ${type.name}")
            when(value) {
                is ApManager -> Unit // Shared immutable AP/key infrastructure has its existing lifetime.
                is Map<*,*> -> for((key,item) in value) { if(key!=null)pending.add(key); if(item!=null)pending.add(item) }
                is Iterable<*> -> for(item in value)if(item!=null)pending.add(item)
                is Array<*> -> for(item in value)if(item!=null)pending.add(item)
                else -> if(type.name.startsWith("org.opentaint.dataflow.bidi.store.")) {
                    for(field in type.declaredFields) if(!java.lang.reflect.Modifier.isStatic(field.modifiers)) {
                        field.isAccessible=true
                        field.get(value)?.let(pending::add)
                    }
                }
            }
        }
        assertTrue(seen.keys.any { it.javaClass.simpleName=="PackedGuidanceCatalog" })
    }

    @Test fun `native C5 with packed guidance preserves full protection annotation`() {
        val f=Fixture(); val packed=FrozenStaticCompletion.Builder(f.ap,f.graph)
        val reference=ReferenceFrozenStaticCompletion.Builder(f.ap,f.graph)
        for(seed in listOf(f.p(AccessPathBase.Argument(0),f.t) to f.c(mark=f.t),
            f.c(mark=f.t) to f.p(AccessPathBase.Return,f.t))) {
            packed.addSeed(f.f.a,seed.first,seed.second)
            reference.addSeed(f.f.a,seed.first,seed.second)
        }
        val actual=packed.build(); val expected=reference.build()
        val original=f.ap.initial(f.p(AccessPathBase.Return,f.t,tail=Tail.EXACT))
        val raw=f.ap.selectedProtection(f.f.fact(AccessPathBase.Argument(0),mark=f.t,layer=Layer.DEMAND),f.ap.markSetOf(f.t.mark))
        val policy=RestrictedInitialPolicy(2,2,Direction.BACKWARD,f.ap.marks)
        fun selected(completion:FrozenCompletion)=DemandStore.Builder(f.ap).apply { withCompletion(completion) }.build()
            .intersect(f.f.a,original,raw,policy).map { it to (it as? TaintTree)?.nonSubsumable }
        assertEquals(selected(expected),selected(actual))
        assertTrue(selected(actual).isNotEmpty())
        assertTrue(selected(actual).any { it.second!=null })
    }

    @Test fun `packed snapshot preserves every ordered native query and callback trace`() {
        val f=Fixture(); val (packed,reference)=f.snapshots()
        fun compare(actual:FrozenCompletion, expected:FrozenCompletion, method:MethodKey) {
            assertEquals(expected.mayNeedInheritedPairs(method),actual.mayNeedInheritedPairs(method))
            assertEquals(expected.mayNeedInheritedEntries(method,f.samples),actual.mayNeedInheritedEntries(method,f.samples))
            for(inherited in listOf(false,true)) {
                val a=if(inherited)actual.visible(method) else actual.local(method)
                val e=if(inherited)expected.visible(method) else expected.local(method)
                assertEquals(e.targetInputs().toList(),a.targetInputs().toList())
                for(sample in f.samples) {
                    assertEquals(e.entries(sample).toList(),a.entries(sample).toList())
                    for(prefix in listOf(false,true)) assertEquals(e.targets(sample,prefix).toList(),a.targets(sample,prefix).toList())
                    assertEquals(e.flowTargets(sample).toList(),a.flowTargets(sample).toList())
                    for(flow in listOf(false,true)) assertEquals(e.incoming(sample,flow).toList(),a.incoming(sample,flow).toList())
                    assertEquals(e.outgoing(sample).toList(),a.outgoing(sample).toList())
                    val initial=f.ap.initial(sample)
                    assertEquals(e.pairs(initial,f.samples).toList(),a.pairs(initial,f.samples).toList())
                    assertEquals(e.hasComposedEndpoints(initial,f.samples),a.hasComposedEndpoints(initial,f.samples))
                    for(mark in listOf(f.t.mark,f.u.mark,f.v.mark,f.group.mark)) {
                        assertEquals(e.markedOutputs(mark).toList(),a.markedOutputs(mark).toList())
                        assertEquals(e.estimatedMarkedOutputs(mark),a.estimatedMarkedOutputs(mark))
                        assertEquals(e.hasMarkedOutput(sample,mark),a.hasMarkedOutput(sample,mark))
                    }
                    for(selection in listOf(StaticLabelSelection.All,StaticLabelSelection.FlowOnly,
                        outputCovering(sample,f.ap.marks),outputComposable(f.t.mark,f.ap.marks))) {
                        val query=StaticRowQuery(selection,mappedGeometryAllowed={it.fact.path.size<=2})
                        fun trace(view:StaticDemandView):Pair<List<StaticGuidanceEdge>,List<StaticGuidanceEdge>> {
                            val calls=ArrayList<StaticGuidanceEdge>()
                            val rows=view.selectedTargets(sample,false,query,StaticCandidateFilter { from,to,marks ->
                                calls+=StaticGuidanceEdge(from,to,marks); calls.size%2==1
                            }).toList()
                            return rows to calls
                        }
                        assertEquals(trace(e),trace(a))
                        fun incoming(view:StaticDemandView):Pair<List<StaticGuidanceEdge>,List<StaticGuidanceEdge>> {
                            val calls=ArrayList<StaticGuidanceEdge>()
                            val rows=view.selectedIncoming(sample,query,StaticCandidateFilter { from,to,marks ->
                                calls+=StaticGuidanceEdge(from,to,marks); calls.size%2==0
                            }).toList()
                            return rows to calls
                        }
                        assertEquals(incoming(e),incoming(a))
                        fun composed(view:StaticDemandView):Pair<Boolean,List<StaticGuidanceEdge>> {
                            val calls=ArrayList<StaticGuidanceEdge>()
                            val answer=view.selectedHasComposedEndpoints(initial,f.samples,query,StaticCandidateFilter { from,to,marks ->
                                calls+=StaticGuidanceEdge(from,to,marks); calls.size%2==1
                            }); return answer to calls
                        }
                        assertEquals(composed(e),composed(a))
                    }
                    for(stop in listOf(1,3,Int.MAX_VALUE)) {
                        fun visits(view:FrozenCompletion):Pair<Boolean,List<Pair<Pattern,Boolean>>> {
                            val trace=ArrayList<Pair<Pattern,Boolean>>()
                            val answer=view.visitPossibleTargets(method,sample) { p,flow -> trace+=p to flow; trace.size<stop }
                            return answer to trace
                        }
                        assertEquals(visits(expected),visits(actual))
                    }
                }
            }
        }
        compare(packed,reference,f.f.a); compare(packed,reference,f.f.b)
        compare(packed,reference,f.f.key(f.f.a.method,"other context"))
        val a=packed.scopedViews().toList(); val e=reference.scopedViews().toList()
        assertEquals(e.map { it.first },a.map { it.first })
        for(i in a.indices) {
            compare(a[i].second,e[i].second,a[i].first.method)
            for(port in listOf(PortId(10),PortId(11),PortId(99)))
                compare(a[i].second.selectExit(port),e[i].second.selectExit(port),a[i].first.method)
        }
        assertEquals(reference.writerAttachments,packed.writerAttachments)
        assertEquals(reference.readerAttachments,packed.readerAttachments)
        assertEquals(reference.seedMemberships,packed.seedMemberships)
    }
}
