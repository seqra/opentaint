package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

class DirectionalMatchingIntegrationTest {
    @Test fun `saved local application and observer agree on role and retain the physical exit`() {
        val f = StoreFixtures()
        val p = AccessPathBase.Argument(0)
        val q = AccessPathBase.Return
        val field = f.field("f")
        val ap = f.manager
        val mode = ApMode(false, Direction.FORWARD, 4)
        val original = ap.initial(f.pattern(p, tail = Tail.STAR, mark = MarkSlot.STAR))
        val deep = ap.initial(f.pattern(p,listOf(field),Tail.STAR,MarkSlot.STAR))
        val actual = f.fact(p,tail=Tail.STAR,mark=MarkSlot.STAR)
        val direct = Record(f.method,Direction.FORWARD,deep,f.fact(q,tail=Tail.STAR,mark=MarkSlot.STAR))
        val opposite = Record(f.method,Direction.BACKWARD,
            ap.initial(f.pattern(q,tail=Tail.STAR,mark=MarkSlot.STAR)),
            f.fact(p,listOf(field),Tail.STAR,MarkSlot.STAR))
        val scope = BlockScope(BlockId(2),PortId(7))
        val exit = PortId(19)
        fun observe(row:Record) = LoopConsumerObservation(f.ops,mode,LoopConsumerViews(scope,false,
            { emptySet() },{ emptySet() },{ sequenceOf(LoopObservedRecord(row,exit)) },
            { _,_ -> emptySequence() },{ _,_,v -> listOf(v) },{ _,_ -> false },{ _,_ -> false },{ true }))
            .observe(original,actual)
        assertTrue(observe(direct).isEmpty)
        val observed = observe(opposite).enclosingResults.single() as LoopEnclosingResult.Data
        assertEquals(scope,observed.scope)
        assertEquals(exit,observed.exit)
        assertSame(original,observed.original)
        assertEquals(q,observed.member.pattern.fact.base)
        assertEquals(Tail.ANY,observed.member.pattern.fact.tail)
        val values = ArrayList<Facts>()
        val out = object:LocalRelationOut {
            override fun data(original:PremiseKey,value:Facts) { values += value }
            override fun target(original:PremiseKey,target:Target) = error("Not a source")
            override fun markRequest(mark:TaintMark) = error("No request")
        }
        val app=LocalRelationApplication(f.ops,mode)
        opposite.forEachNativeReversedAt(f.ops.leaves(actual).single()) { read,flag ->
            assertTrue(app.applyNativeRecordRead(actual,original,read,flag,out))
        }
        assertEquals(observed.member.pattern,f.ops.leaves(values.single()).single())
        assertEquals(Layer.DEMAND,values.single().layer)
    }

    @Test fun `current ND Target waits for every role-admitted member`() {
        val f=StoreFixtures();val ap=f.manager
        val x=AccessPathBase.Argument(0);val y=AccessPathBase.Argument(1)
        val field=f.field("f");val t=MarkSlot.Concrete(f.mark("T"));val u=MarkSlot.Concrete(f.mark("U"))
        val first=ap.initial(f.pattern(x,listOf(field),mark=t))
        val second=ap.initial(f.pattern(y,mark=u))
        val callerFirst=ap.initial(f.pattern(x,mark=t))
        val parent=BlockScope.ROOT;val child=BlockScope(BlockId(2),PortId(4))
        val results=ArrayList<Pair<PremiseKey,Target>>()
        val links=BlockSummaryLinks(f.ops,ApMode(false,Direction.FORWARD,4),child,
            { _,_,_,_,_,_ -> error("No data") },{ _,p,target -> results += p to target },{ _,_,_ -> error("No request") })
        links.publishTargets(listOf(TargetSummary(ap.union(first,second),Target.DemandTarget)))
        fun offer(p:PremiseKey,value:Facts) {
            links.offer(LocalLink(parent,PortId(9),p,value.layer,child),value)
            while(links.hasPending)links.drain(1)
        }
        offer(callerFirst,f.fact(x,tail=Tail.STAR,mark=t,layer=Layer.DEMAND))
        offer(second,f.fact(y,mark=u))
        assertTrue(results.isEmpty(),"The rejected STAR arm must not complete ND")
        offer(callerFirst,f.fact(x,listOf(field),mark=t,layer=Layer.DEMAND))
        assertEquals(setOf(callerFirst,second),results.single().first.members.toSet())
        assertEquals(Target.DemandTarget,results.single().second)
    }

    @Test fun `run1 ordinary and static canonical prefixes match without an exemption`() {
        val f=StoreFixtures();val ap=f.manager;val mode=ApMode(true,Direction.FORWARD,1)
        val p=AccessPathBase.Argument(0);val field=f.field("f")
        val root=ap.initial(f.pattern(p,tail=Tail.STAR,mark=MarkSlot.STAR))
        val actual=f.fact(p,tail=Tail.STAR,mark=MarkSlot.STAR)
        validateRun1Initial(root,1)
        assertNotNull(f.ops.matchSummary(actual,root,mode,false,SummaryMatchRole.CURRENT))
        val deep=ap.initial(f.pattern(p,listOf(field),Tail.STAR,MarkSlot.STAR))
        assertNull(f.ops.matchSummary(actual,deep,mode,false,SummaryMatchRole.CURRENT))
        val clazz=ap.accessors.index(ClassStaticAccessor("C"))
        val static=ap.initial(f.pattern(STATIC,listOf(clazz,field),Tail.STAR,MarkSlot.STAR))
        validateRun1Initial(static,1)
        val pool=f.fact(STATIC,listOf(clazz,field),Tail.STAR,MarkSlot.STAR)
        assertNotNull(f.ops.matchSummary(pool,static,mode,false,SummaryMatchRole.CURRENT))
        val classMarker=ap.initial(f.pattern(STATIC,listOf(clazz),mark=MarkSlot.Concrete(f.mark("T"))))
        validateRun1Initial(classMarker,1)
        assertNotNull(f.ops.matchSummary(f.ops.startFact(classMarker,mode),classMarker,mode,false,SummaryMatchRole.CURRENT))
    }

    @Test fun `field microedge and native operation predicate keep STAR ancestry`() {
        val f=StoreFixtures();val p=AccessPathBase.Argument(0);val q=AccessPathBase.Return;val field=f.field("f")
        val actual=f.fact(p,tail=Tail.STAR,mark=MarkSlot.STAR)
        val initial=f.manager.initial(f.pattern(p,tail=Tail.STAR,mark=MarkSlot.STAR))
        val mode=ApMode(false,Direction.FORWARD,4)
        val out=CollectingOut()
        f.ops.applyEdge(actual,initial,starEdge(p,listOf(field),q,emptyList()),true,mode,out)
        assertEquals(Tail.ANY,f.ops.leaves(out.results.single()).single().fact.tail)
        assertNotNull(f.ops.satisfying(actual,f.pattern(p,listOf(field),Tail.STAR,MarkSlot.STAR),mode))
    }

    @Test fun `overlapping inverse of a uniform source retains typed Target discharge`() {
        val f=StoreFixtures();val ap=f.manager;val q=AccessPathBase.Return
        val g=f.field("actual excluded");val h=f.field("source excluded")
        val t=MarkSlot.Concrete(f.mark("T"))
        val old=f.fact(q,tail=Tail.ANY_TAINT,mark=t,exclusion=ExclusionSet.of(h))
        val read=assertNotNull(reverseNativeRecordLeaf(Direction.FORWARD,ap.zero.toPattern(),
            Conclusion(f.ops.leaves(old).single().fact,ExclusionSet.of(h),false)))
        val actual=f.fact(q,tail=Tail.STAR,mark=t,exclusion=ExclusionSet.of(g),layer=Layer.DEMAND)
        val original=ap.initial(f.pattern(q,tail=Tail.STAR,mark=t))
        val targets=ArrayList<Target>()
        assertTrue(LocalRelationApplication(f.ops,ApMode(false,Direction.BACKWARD,4))
            .applyNativeRecordRead(actual,original,read,false,object:LocalRelationOut {
                override fun data(original:PremiseKey,value:Facts) = error("Source inverse is terminal")
                override fun target(p:PremiseKey,target:Target) { assertSame(original,p);targets += target }
                override fun markRequest(mark:TaintMark) = error("No mark request")
            }))
        assertEquals(listOf<Target>(Target.DemandTarget),targets)
    }

    @Test fun `precise and delayed coarse calls retain both complete-driver findings`() = DriverFixtures().use { f ->
        val p=f.program
        fun straight(n:Int)=List(n){if(it+1<n)listOf(it+1)else emptyList()}
        val root=p.method("main",straight(4),3).key()
        val helper=p.method("helper",straight(3),2).key()
        val wrapper=p.method("wrapper",straight(3),2).key()
        val early=AccessPathBase.LocalVar(0);val late=AccessPathBase.LocalVar(1)
        val e=AccessPathBase.LocalVar(2);val l=AccessPathBase.LocalVar(3)
        val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
        val a=p.field("a");val b=p.field("b");val c=p.field("c");val ff=p.field("f");val gg=p.field("g")
        val t=MarkSlot.Concrete(p.mark("T"))
        p.entry(root,RuleStatement(f.summary(ZERO_KEEP,
            PathEdge(ZERO_FACT,p.pattern(early,listOf(ff,gg),Tail.EXACT,t).fact,ExclusionSet.Empty),
            PathEdge(ZERO_FACT,p.pattern(late,listOf(a,b,c,ff,gg),Tail.EXACT,t).fact,ExclusionSet.Empty)),StatementSummary.EMPTY,emptyList()))
        fun call(callee:MethodKey,from:AccessPathBase,path:List<Int>,to:AccessPathBase)=CallPlan(setOf(from,to),listOf(
            CallStage.Edges(BEFORE,AFTER,PASS_OVER,f.summary(keepEdge(early),keepEdge(late),keepEdge(e))),
            CallStage.Edges(BEFORE,BOUND,BIND_IN,f.summary(ZERO_KEEP,starEdge(from,path,arg,emptyList()))),
            CallStage.Actions(BOUND,ADDED,emptyList()),CallStage.Callees(ADDED,RETURNED,listOf(callee)),
            CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
            CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,f.summary(ZERO_KEEP,starEdge(ret,emptyList(),to,emptyList())))),emptyList(),BEFORE,AFTER)
        p.call(root,1,call(helper,early,emptyList(),e));p.call(root,2,call(wrapper,late,emptyList(),l))
        p.call(wrapper,1,call(helper,arg,listOf(a,b,c),ret))
        p.statement(helper,1,MicroEdgeBuilder().apply{read(ret,arg,listOf(ff,gg))}.build())
        val se=SinkRule(f.rule("early sink T"),0,listOf(p.pattern(e,mark=t)),emptyList())
        val sl=SinkRule(f.rule("late sink T"),0,listOf(p.pattern(l,mark=t)),emptyList())
        p.exit(root,3,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,listOf(se,sl)),false,emptySet()))
        val result=f.driver(FixedLimits(listOf(1,1,2,3,4,5,6,7,8)),budget=20.seconds,run1MarkMode=MarkMode.FULL).analyze(listOf(root))
        assertEquals(setOf(se.rule.id,sl.rule.id),result.entries.map{it.descriptor.key.ruleId}.toSet())
        assertEquals(RunStatus.COMPLETE,result.end.status)
    }
}
