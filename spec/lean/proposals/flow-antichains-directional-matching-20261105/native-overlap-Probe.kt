package org.opentaint.dataflow.bidi.external
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.*

private fun quote(s: String): String = "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"") + "\""
private fun json(x: Any?): String = when(x) {
 null -> "null"; is String -> quote(x); is Boolean, is Number -> x.toString()
 is Map<*, *> -> x.entries.joinToString(",", "{", "}") { quote(it.key.toString()) + ":" + json(it.value) }
 is Iterable<*> -> x.joinToString(",", "[", "]") { json(it) }; else -> error("JSON")
}
fun main() {
 val f = StoreFixtures(); val ap = f.manager; val ops = f.ops
 val p = AccessPathBase.Argument(0); val q = AccessPathBase.Return
 val aa = f.field("prefixA"); val bb = f.field("prefixB")
 val gg = f.field("actualExcludedG"); val hh = f.field("storedExcludedH"); val ii = f.field("oldInputExcludedI")
 val t = f.mark("T"); val u = f.mark("U")
 val old = ap.initial(f.pattern(p, listOf(aa,bb), Tail.ANY_TAINT, MarkSlot.STAR, ExclusionSet.of(ii)))
 val output = f.fact(q, tail=Tail.ANY_TAINT, mark=MarkSlot.Star(MarkExclusions.of(ap.marks,listOf(u))), exclusion=ExclusionSet.of(hh))
 val record = Record(f.method, Direction.FORWARD, old, output, BlockScope(BlockId(2),PortId(20)), PortId(80))
 val mode = ApMode(false,Direction.BACKWARD,5)
 fun desc(x: Facts) = linkedMapOf("layer" to x.layer.name, "rows" to ops.leaves(x).map { pat -> linkedMapOf("base" to pat.fact.base.toString(),"path" to pat.fact.path,"tail" to pat.fact.tail.name,"mark" to pat.fact.mark.toString(),"E" to pat.exclusion.toString()) }.toList())
 fun nativeApply(actual: Facts, view: RecordLeafView): Pair<List<Facts>,List<Int>> {
  val results=ArrayList<Facts>();val requests=ArrayList<Int>()
  ops.applyRecordLeaf(actual,view,false,mode,object:ApOut {
   override fun result(fact:Facts) { results += fact }
   override fun markRequest(mark:TaintMark) { requests += mark.id }
  }, original=ap.initial(f.pattern(q, tail=Tail.STAR, mark=MarkSlot.STAR)))
  return results to requests
 }
 val cases = ArrayList<Map<String,Any?>>()
 for ((name,tail,layer) in listOf(Triple("STAR FLOW",Tail.STAR,Layer.NORMAL),Triple("MAY FLOW",Tail.ANY,Layer.DEMAND),Triple("MUST FLOW",Tail.ANY_TAINT,Layer.NORMAL))) {
  val actual=f.fact(q,tail=tail,mark=MarkSlot.Star(MarkExclusions.of(ap.marks,listOf(t))),exclusion=if(tail==Tail.ANY)ExclusionSet.Empty else ExclusionSet.of(gg),layer=layer)
  var view:RecordLeafView?=null
  record.forEachReversedAt(ops.leaves(actual).single()) { v,_ -> check(view==null);view=v }
  val v=checkNotNull(view)
  val matched=ops.satisfying(actual,v.premise,mode,record=true)
  val raw=nativeApply(actual,v)
  val narrowed=if(tail==Tail.STAR) f.fact(q,tail=tail,mark=MarkSlot.Star(MarkExclusions.of(ap.marks,listOf(t))),exclusion=ExclusionSet.of(intArrayOf(gg,hh)),layer=layer) else actual
  val projectionSelected=ops.satisfying(narrowed,v.premise,mode,record=true)
  if(tail==Tail.STAR) check(projectionSelected!=null)
  val projected=nativeApply(projectionSelected ?: narrowed,v)
  check(raw.second.isEmpty() && projected.second.isEmpty())
  check(raw.first.single()==projected.first.single())
  check(raw.first.single().layer==Layer.DEMAND)
  val leaf=ops.leaves(raw.first.single()).single()
  check(leaf.fact.base==p && leaf.fact.path==listOf(aa,bb) && leaf.fact.tail==Tail.ANY && leaf.exclusion==ExclusionSet.Empty)
  check((leaf.fact.mark as MarkSlot.Star).excluded==MarkExclusions.of(ap.marks,listOf(t,u)))
  if(tail==Tail.STAR)check(matched==null)
  cases += linkedMapOf("actualKind" to name,"nativeSelection" to matched?.let(::desc),"actual" to desc(actual),"viewPremise" to v.premise.toString(),"viewResult" to v.result.toString(),"nativeRawApplyOutputs" to raw.first.map(::desc),"intersectionActual" to desc(narrowed),"nativeIntersectionSelection" to projectionSelected?.let(::desc),"nativeIntersectionApplyOutputs" to projected.first.map(::desc),"requests" to raw.second)
 }
 val concrete = ArrayList<Map<String,Any?>>()
 for (oldTail in listOf(Tail.EXACT,Tail.ANY_TAINT)) for (actualLayer in listOf(Layer.NORMAL,Layer.DEMAND)) {
  val oldP=ap.initial(f.pattern(p,listOf(aa,bb),oldTail,MarkSlot.Concrete(t),if(oldTail==Tail.ANY_TAINT)ExclusionSet.of(ii) else ExclusionSet.Empty))
  val oldG=f.fact(q,tail=Tail.ANY_TAINT,mark=MarkSlot.Concrete(t),exclusion=ExclusionSet.of(hh))
  val r=Record(f.method,Direction.FORWARD,oldP,oldG)
  val rawPlain=f.fact(q,tail=Tail.STAR,mark=MarkSlot.Concrete(t),exclusion=ExclusionSet.of(gg),layer=actualLayer) as TaintTree
  val raw=rawPlain.withProtection(rawPlain.root)
  val projectedPlain=f.fact(q,tail=Tail.STAR,mark=MarkSlot.Concrete(t),exclusion=ExclusionSet.of(intArrayOf(gg,hh)),layer=actualLayer) as TaintTree
  val projection=projectedPlain.withProtection(rawPlain.root)
  var read:RecordLeafView?=null
  r.forEachReversedAt(ops.leaves(raw).single()) { v,_ -> check(read==null);read=v }
  val v=checkNotNull(read)
  check(ops.satisfying(raw,v.premise,mode,record=true)==null)
  val matched=checkNotNull(ops.satisfying(projection,v.premise,mode,record=true))
  val oldApp=nativeApply(raw,v)
  val bridgeApp=nativeApply(matched,v)
  check(oldApp.first.single()==bridgeApp.first.single())
  val out=bridgeApp.first.single()
  check(out.layer==if(oldTail==Tail.ANY_TAINT)Layer.DEMAND else actualLayer)
  check((out as TaintTree).nonSubsumable!=null)
  concrete += linkedMapOf("oldPremise" to oldP.toString(),"oldOutput" to desc(oldG),"actual" to desc(raw),"actualProtected" to true,"nativeOldSelection" to null,"projectedActual" to desc(projection),"nativeProjectedSelection" to desc(matched),"viewPremise" to v.premise.toString(),"viewResult" to v.result.toString(),"nativeRawApplyOutputs" to oldApp.first.map(::desc),"nativeBridgeOutputs" to bridgeApp.first.map(::desc),"protectionPreserved" to true,"requests" to bridgeApp.second)
 }
 println(json(linkedMapOf("state" to "PASS","cases" to cases,"concreteCases" to concrete,"sourceRecord" to linkedMapOf("producerDirection" to record.direction.name,"P" to old.toString(),"output" to desc(output),"scope" to record.scope.toString(),"exit" to record.exit.toString(),"readerScope" to record.scopeIn(mode.direction).toString(),"readerExit" to record.exitIn(mode.direction).toString()),"limits" to "Native AP application only; direct invocation deliberately bypasses old rejected Summary selector to test the proposed overlap adapter path; no production changes or project run.")))
}
