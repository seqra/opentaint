import java.util.*;
import org.opentaint.dataflow.ap.ifds.AccessPathBase;
import org.opentaint.dataflow.bidi.ap.*;
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures;

/** Bounded search only. Does not prove the unrestricted current-route obligation. */
public class NormalTargetCurrentGateControl {
 public static void main(String[] args) throws Exception {
  try(var f=new MethodAnalysisFixtures()) {
   var ap=f.getManager(); var ops=f.getOps();
   var arg=AccessPathBase.Argument.Companion.create(0);
   var empty=ExclusionSet.Empty.INSTANCE;
   int id=(int)MethodAnalysisFixtures.class.getMethod("mark-sAff8Ok",String.class).invoke(f,"T");
   var ctor=MarkSlot.Concrete.class.getDeclaredConstructor(int.class,kotlin.jvm.internal.DefaultConstructorMarker.class);
   var t=ctor.newInstance(id,null);
   int a=f.field("a"),b=f.field("b");
   List<List<Integer>> paths=List.of(List.of(),List.of(a),List.of(b),List.of(a,a),List.of(a,b),List.of(b,a),List.of(b,b));
   List<ExclusionSet> exclusions=List.of(empty,ExclusionSet.Companion.of(a),ExclusionSet.Companion.of(b));
   var policy=new RestrictedInitialPolicy(3,2,Direction.FORWARD,ap.getMarks());
   var mode=new ApMode(false,Direction.FORWARD,2,MarkMode.FULL);
   var actuals=new ArrayList<Facts>(); var demands=new ArrayList<Pattern>();
   for(var p:paths) {
    for(var tail:List.of(Tail.EXACT,Tail.ANY,Tail.ANY_TAINT)) {
     for(var e:(tail==Tail.ANY_TAINT ? exclusions : List.<ExclusionSet>of(empty)))
      actuals.add(f.fact(arg,p,tail,t,e,tail==Tail.ANY?Layer.DEMAND:Layer.NORMAL));
    }
    for(var tail:List.of(Tail.EXACT,Tail.ANY,Tail.STAR)) {
     for(var e:(tail==Tail.STAR ? exclusions : List.<ExclusionSet>of(empty)))
      demands.add(f.pattern(arg,p,tail,t,e));
    }
   }
   int normalInitialInstances=0,matchedInputs=0,emptyMatches=0;
   String example="";
   for(var d:demands) {
    var pair=new DemandPattern(d,ap.getZero().toPattern());
    for(var producer:actuals) for(var initial:ops.emit(pair,producer,policy)) {
     if(ops.startFact(initial,mode).getLayer()!=Layer.NORMAL) continue;
     normalInitialInstances++;
     for(var consumer:actuals) {
      if(ops.satisfying(consumer,initial,mode,false)==null) continue;
      matchedInputs++;
      if(ops.emit(pair,consumer,policy).isEmpty()) {
       emptyMatches++; if(example.isEmpty()) example="d="+d+"; initial="+initial+"; actual="+consumer;
      }
     }
    }
   }
   System.out.println("{\"status\":\"PASS\",\"scope\":\"bounded concrete NORMAL-initial current-match search\",\"paths\":7,\"demandPatterns\":"+demands.size()+",\"actualFacts\":"+actuals.size()+",\"normalInitialInstances\":"+normalInitialInstances+",\"matchedConsumerFacts\":"+matchedInputs+",\"emptyEmissionMatches\":"+emptyMatches+"}");
   if(emptyMatches!=0) throw new AssertionError(example);
  }
 }
}
