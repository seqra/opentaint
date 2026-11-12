package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.fixtures.HandOffFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class HandoffCompactorTest {
    private val p = AccessPathBase.Argument(0)
    private val q = AccessPathBase.Argument(1)
    private val ret = AccessPathBase.Return

    @Test fun `R1 and R2 select one final service basis in either arrival order`() {
        HandOffFixtures(3).use { f ->
            val t = MarkSlot.Concrete(f.mark("T"))
            val a = f.field("a")
            val owner = HandoffOwner(f.key())
            val rows = listOf(
                HandoffOrigin(owner, false, listOf(PairedDemand(DemandEntry.Data(f.pattern(ret, mark=t)),
                    DemandExit.Data(f.pattern(p, listOf(a), Tail.ANY, t)))), "must"),
                HandoffOrigin(owner, false, listOf(PairedDemand(DemandEntry.Data(f.pattern(ret, tail=Tail.STAR, mark=t)),
                    DemandExit.Data(f.pattern(p, listOf(a), Tail.STAR, t)))), "star"),
            )
            for (offered in listOf(rows, rows.reversed())) {
                val selected = HandoffCompactor(f.manager).select(offered)
                assertEquals(1, selected.kept.size)
                assertEquals(1, selected.certificates.size)
                assertTrue(selected.certificates.values.flatten().all { it.provider in selected.kept })
                assertEquals("star", selected.kept.single().orderKey)
            }
        }
    }

    @Test fun `ND removal requires every member and output leaf and final providers`() {
        HandOffFixtures(3).use { f ->
            val owner = HandoffOwner(f.key())
            val t = MarkSlot.Concrete(f.mark("T"))
            fun row(input: AccessPathBase, field: Int) = PairedDemand(
                DemandEntry.Data(f.pattern(ret, listOf(field), mark=t)), DemandExit.Data(f.pattern(input, mark=t)))
            val a=f.field("a"); val b=f.field("b")
            val all = listOf(row(p,a), row(q,a), row(p,b), row(q,b))
            val nd = HandoffOrigin(owner, false, all, "0-nd")
            val arms = all.mapIndexed { i, row -> HandoffOrigin(owner, false, listOf(row), "arm-$i") }
            assertTrue(nd in HandoffCompactor(f.manager).select(listOf(nd)+arms.dropLast(1)).kept)
            val full = HandoffCompactor(f.manager).select(listOf(nd)+arms)
            assertFalse(nd in full.kept)
            assertEquals(8, full.certificates.getValue(nd).size) // two services for every obligation
            assertTrue(full.certificates.values.flatten().all { it.provider in full.kept })
        }
    }

    @Test fun `removed providers are rebound to final origins and equivalent origins cannot all disappear`() {
        HandOffFixtures(3).use { f ->
            val row = PairedDemand(DemandEntry.Data(f.pattern(ret)), DemandExit.Data(f.pattern(p)))
            val origins = (0..3).map { HandoffOrigin(HandoffOwner(f.key()), false, listOf(row), "$it") }
            val result = HandoffCompactor(f.manager).select(origins)
            assertEquals(listOf(origins.last()), result.kept)
            assertEquals(3, result.certificates.size)
            assertTrue(result.certificates.values.flatten().all { it.provider == origins.last() })
        }
    }

    @Test fun `protection controls context and physical ports cannot cover each other`() {
        HandOffFixtures(3).use { f ->
            val row = PairedDemand(DemandEntry.Target, DemandExit.Data(f.pattern(p)))
            val scope = BlockScope(BlockId(5), PortId(11))
            val rows = listOf(
                HandoffOrigin(HandoffOwner(f.key()), false, listOf(row), "method"),
                HandoffOrigin(HandoffOwner(f.key()), true, listOf(row), "protected"),
                HandoffOrigin(HandoffOwner(f.key("other")), false, listOf(row), "context"),
                HandoffOrigin(HandoffOwner(f.key(),scope,PortId(12)), false, listOf(row), "block"),
                HandoffOrigin(HandoffOwner(f.key(),scope,PortId(13)), false, listOf(row), "exit"),
                HandoffOrigin(HandoffOwner(f.key()), false, listOf(row.copy(entry=DemandEntry.Zero)), "zero"),
            )
            assertEquals(rows.toSet(), HandoffCompactor(f.manager).select(rows).kept.toSet())
        }
    }

    @Test fun `R3 cross-lane MAY alone is not a service proof`() {
        HandOffFixtures(3).use { f ->
            val owner = HandoffOwner(f.key())
            val a = f.field("a")
            val x = HandoffOrigin(owner,false,listOf(PairedDemand(DemandEntry.Data(f.pattern(ret,listOf(a))),
                DemandExit.Data(f.pattern(p)))),"x")
            val y = HandoffOrigin(owner,false,listOf(PairedDemand(DemandEntry.Data(f.pattern(ret,tail=Tail.ANY)),
                DemandExit.Data(f.pattern(p)))),"y")
            assertEquals(setOf(x,y),HandoffCompactor(f.manager).select(listOf(x,y)).kept.toSet())
        }
    }
    @Test fun `native late FULL point services equal canonical keys including exclusions and companions`() {
        HandOffFixtures(3).use { f ->
            val t = MarkSlot.Concrete(f.mark("T")); val u = MarkSlot.Concrete(f.mark("U"))
            val field=f.field("a"); val excluded=ExclusionSet.of(f.field("b"))
            val keys=HandoffServiceKeys(f.manager)
            for (run in listOf(3,4,7)) {
                val policy=RestrictedInitialPolicy(run,4,if (run%2==0) Direction.BACKWARD else Direction.FORWARD)
                for (base in listOf(p,ret,AccessPathBase.This,AccessPathBase.LocalVar(8),AccessPathBase.Exception)) {
                    val exact=f.pattern(base,listOf(field),Tail.EXACT,t)
                    for (e in listOf(ExclusionSet.Empty,excluded)) {
                        val star=f.pattern(base,listOf(field),Tail.STAR,t,e)
                        assertEquals(keys.entry(DemandEntry.Data(exact)),keys.entry(DemandEntry.Data(star)))
                        for (path in listOf(emptyList(),listOf(field),listOf(field,field)))
                            for (tail in Tail.entries) for (mark in listOf(t,u,MarkSlot.STAR))
                                for (layer in Layer.entries) {
                                    val actual=f.pattern(base,path,tail,mark)
                                    assertEquals(policy.emitAdmissions(exact,actual,layer),policy.emitAdmissions(star,actual,layer))
                                    assertEquals(policy.canStoreInitial(exact,actual),policy.canStoreInitial(star,actual))
                                }
                    }
                }
            }
        }
    }

    @Test fun `native paired output MAY and STAR service agrees on concrete and FLOW results`() {
        HandOffFixtures(3).use { f ->
            val t=MarkSlot.Concrete(f.mark("T")); val field=f.field("a")
            for (mark in listOf(t,MarkSlot.STAR)) {
                val may=f.pattern(p,listOf(field),Tail.ANY,mark)
                val star=may.copy(fact=may.fact.copy(tail=Tail.STAR))
                assertEquals(HandoffServiceKeys(f.manager).output(DemandExit.Data(may)),DemandExit.Data(star))
                for (path in listOf(emptyList(),listOf(field),listOf(field,field))) for (tail in Tail.entries) {
                    val raw=Conclusion(PathFact(p,path,tail,mark),ExclusionSet.Empty,tail==Tail.ANY)
                    assertEquals(restrictConclusionOnly(raw,may),restrictConclusionOnly(raw,star))
                }
            }
        }
    }

    @Test fun `real late handoff compacts point outputs and preserves frozen summaries`() {
        HandOffFixtures(3).use { f ->
            val key=f.key(); val original=f.initial(p)
            f.summary(key,original,f.fact(ret,tail=Tail.EXACT,layer=Layer.DEMAND))
            f.summary(key,original,f.fact(ret,tail=Tail.STAR,layer=Layer.DEMAND))
            val result=f.result()
            val before=result.analyzers.single().summaries.all().toList()
            val handoff=HandOff.of(f.config,result,f.shared)
            assertEquals(1,handoff.demandEdges.getValue(key))
            assertEquals(before,result.analyzers.single().summaries.all().toList())
            assertEquals(1,handoff.demand.near(key,f.pattern(ret,tail=Tail.ANY,mark=MarkSlot.STAR)).size)
        }
    }

    @Test fun `retained actual demand stores preserve complete C2 and C5 services`() {
        HandOffFixtures(3).use { f ->
            val owner=HandoffOwner(f.key()); val a=f.field("a"); val b=f.field("b")
            val t=MarkSlot.Concrete(f.mark("T")); val u=MarkSlot.Concrete(f.mark("U"))
            val x=HandoffOrigin(owner,false,listOf(PairedDemand(
                DemandEntry.Data(f.pattern(ret,listOf(a),mark=t)),
                DemandExit.Data(f.pattern(p,tail=Tail.STAR,mark=t)))),"0-x")
            val z=HandoffOrigin(owner,false,listOf(PairedDemand(
                DemandEntry.Data(f.pattern(ret,listOf(a),tail=Tail.STAR,mark=t)),
                DemandExit.Data(f.pattern(q,tail=Tail.STAR,mark=t)))),"1-z")
            val y=HandoffOrigin(owner,false,listOf(PairedDemand(
                DemandEntry.Data(f.pattern(ret,tail=Tail.ANY,mark=t)),
                DemandExit.Data(f.pattern(p,tail=Tail.ANY,mark=t)))),"2-y")
            val origins=listOf(x,z,y)
            val chosen=HandoffCompactor(f.manager).select(origins)
            assertFalse(x in chosen.kept)
            assertEquals(setOf(z,y),chosen.kept.toSet())
            fun store(rows:List<HandoffOrigin>)=DemandStore.Builder(f.manager).apply {
                rows.forEach { origin -> origin.rows.forEach { add(owner.method,it) } }
            }.build()
            val before=store(origins); val after=store(chosen.kept)
            for (run in listOf(3,4,7)) {
                val policy=before.admissionPolicy(run,4,if (run%2==0) Direction.BACKWARD else Direction.FORWARD)
                for (path in listOf(emptyList(),listOf(a),listOf(b),listOf(a,b)))
                    for (tail in Tail.entries) for (mark in listOf(t,u,MarkSlot.STAR))
                        for (layer in Layer.entries) {
                            val e=if (tail==Tail.STAR || tail==Tail.ANY_TAINT) ExclusionSet.of(b) else ExclusionSet.Empty
                            val actual=f.fact(ret,path,tail,mark,e,if (tail==Tail.ANY) Layer.DEMAND else layer)
                            assertEquals(before.initials(owner.method,actual,policy),after.initials(owner.method,actual,policy),
                                "C2 run=$run path=$path tail=$tail mark=$mark layer=$layer")
                            if (tail==Tail.ANY || tail==Tail.ANY_TAINT && policy.direction==Direction.BACKWARD ||
                                mark is MarkSlot.Star && tail==Tail.EXACT && e!=ExclusionSet.Empty) continue
                            val initial=f.initial(ret,path,tail,mark,e)
                            for (outBase in listOf(p,q)) for (outTail in Tail.entries) {
                                val raw=f.fact(outBase,listOf(a),outTail,t,layer=if (outTail==Tail.ANY) Layer.DEMAND else layer)
                                assertEquals(before.intersect(owner.method,initial,raw,policy).toSet(),
                                    after.intersect(owner.method,initial,raw,policy).toSet(),
                                    "C5 run=$run path=$path tail=$tail out=$outBase/$outTail")
                            }
                        }
            }
        }
    }

}
