import java.util.*;
import org.opentaint.dataflow.ap.ifds.AccessPathBase;
import org.opentaint.dataflow.bidi.ap.*;
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures;
import org.opentaint.dataflow.bidi.store.*;

/** Production AP control only. Target is not implemented or simulated by this class. */
public class TerminalBoundaryApControl {
  static void check(boolean value, String name) { if (!value) throw new AssertionError(name); }
  public static void main(String[] args) throws Exception {
    try (var f = new MethodAnalysisFixtures()) {
      var ap=f.getManager(); var ops=f.getOps();
      var e=ExclusionSet.Empty.INSTANCE;
      var arg=AccessPathBase.Argument.Companion.create(0);
      var star=MarkSlot.Companion.getSTAR();
      int mark=(int)MethodAnalysisFixtures.class.getMethod("mark-sAff8Ok", String.class).invoke(f,"T");
      var ctor=MarkSlot.Concrete.class.getDeclaredConstructor(int.class,kotlin.jvm.internal.DefaultConstructorMarker.class);
      var t=ctor.newInstance(mark,null);
      var modeF=new ApMode(false,Direction.FORWARD,2,MarkMode.FULL);
      var modeB=new ApMode(false,Direction.BACKWARD,3,MarkMode.FULL);
      var source= f.fact(arg,List.of(),Tail.EXACT,t,e,Layer.NORMAL);
      var may=new PathEdge(new PathFact(arg,List.of(),Tail.STAR,star),
                           new PathFact(arg,List.of(),Tail.ANY,star),e,e,e);
      var mayOut=new CollectingOut();
      ops.applyEdge(source,ap.getZero(),may,false,modeF,mayOut,true,null,false);
      check(mayOut.getResults().size()==1,"may edge one result");
      var actual=mayOut.getResults().get(0);
      check(actual.getLayer()==Layer.DEMAND,"real may edge creates DEMAND actual");
      var exact=f.pattern(arg,List.of(),Tail.EXACT,t,e);
      var policy=new RestrictedInitialPolicy(3,2,Direction.FORWARD,ap.getMarks());
      var initials=ops.emit(new DemandPattern(exact,ap.getZero().toPattern()),actual,policy);
      check(initials.size()==1,"C2 exact guide admits one initial");
      var initial=initials.get(0);
      check(initial.getTail()==Tail.EXACT,"C2 initial is exact");
      var start=ops.startFact(initial,modeF);
      check(start.getLayer()==Layer.NORMAL,"callee exact initial starts NORMAL");
      check(ops.checkMark(start,exact,modeF,null) instanceof MarkCheck.Holds,
            "normal callee fact triggers actual sink mark check");
      check(ops.satisfying(actual,initial,modeF,false)!=null,
            "original DEMAND actual matches current concrete callee premise");
      check(!initials.isEmpty(),"example preserves selected call gate");

      // Production field-limit witness: F3 limit 2 is DEMAND; F5 limit 4 can be NORMAL.
      var b=AccessPathBase.LocalVar.Companion.create(99);
      var deepPath=List.of(f.field("f"),f.field("g"),f.field("h"));
      var deepSource=f.fact(b,deepPath,Tail.EXACT,t,e,Layer.NORMAL);
      var read=new PathEdge(new PathFact(b,deepPath,Tail.STAR,star),
                            new PathFact(arg,List.of(),Tail.STAR,star),e,e,e);
      var limited2=new CollectingOut(); ops.limit(deepSource,2,limited2);
      check(limited2.getResults().size()==1 && limited2.getResults().get(0).getLayer()==Layer.DEMAND,
            "limit 2 cuts a named depth-3 source into DEMAND");
      var read2=new CollectingOut();
      ops.applyEdge(limited2.getResults().get(0),ap.getZero(),read,false,modeF,read2,false,null,false);
      check(read2.getResults().size()==1 && read2.getResults().get(0).getLayer()==Layer.DEMAND,
            "reading the depth-3 field from cut source gives DEMAND call input");
      var deepInitials=ops.emit(new DemandPattern(exact,ap.getZero().toPattern()),read2.getResults().get(0),policy);
      check(deepInitials.size()==1 && ops.startFact(deepInitials.get(0),modeF).getLayer()==Layer.NORMAL,
            "cut-source input still admits NORMAL exact sink-wrapper initial");
      var limited4=new CollectingOut(); ops.limit(deepSource,4,limited4);
      var read4=new CollectingOut();
      ops.applyEdge(limited4.getResults().get(0),ap.getZero(),read,false,
                    new ApMode(false,Direction.FORWARD,4,MarkMode.FULL),read4,false,null,false);
      check(read4.getResults().size()==1 && read4.getResults().get(0).getLayer()==Layer.NORMAL,
            "limit 4 would deliver NORMAL input if the configured source is permitted");
      var genEdge=new PathEdge(ap.getZero().toPattern().getFact(),
                             new PathFact(b,deepPath,Tail.EXACT,t),e,e,e);
      var reversedGen=ops.reverse(genEdge);
      var noRequirement=new CollectingOut();
      ops.applyEdge(Reach.NORMAL,ap.getZero(),reversedGen,false,modeB,noRequirement,false,null,false);
      check(noRequirement.getResults().isEmpty(),"backward control ZERO cannot trigger the actual reversed GEN");
      var withRequirement=new CollectingOut();
      ops.applyEdge(deepSource,ap.getZero(),reversedGen,false,modeB,withRequirement,false,null,false);
      check(withRequirement.getResults().size()==1 && withRequirement.getResults().get(0) instanceof Reach,
            "marked field requirement does trigger actual reversed GEN");

      var reqLimit1=new CollectingOut(); ops.limit(deepSource,1,reqLimit1);
      var cutRequirement=new CollectingOut();
      ops.applyEdge(reqLimit1.getResults().get(0),ap.getZero(),reversedGen,false,
                    new ApMode(false,Direction.BACKWARD,1,MarkMode.FULL),cutRequirement,false,null,false);
      check(cutRequirement.getResults().size()==1 && cutRequirement.getResults().get(0) instanceof Reach,
            "first backward limit-1 marked requirement still triggers local GEN");

      // A void sink wrapper's ordinary p->p AP record gives no backward ZERO query.
      var owner=f.getStore().key("M",0);
      f.getRecords().add(new org.opentaint.dataflow.bidi.store.Record(owner,Direction.FORWARD,initial,start));
      var zero=ap.getZero().toPattern();
      var found=f.getRecords().byExit(owner,zero).iterator();
      check(!found.hasNext(),"ordinary AP p->p record cannot answer ZERO query");

      // Existing forward normal GEN record 0->ret needs no new source hit to replay forward.
      var ret=AccessPathBase.Return.INSTANCE;
      var genOwner=f.getStore().key("S",0);
      var retFact=f.fact(ret,List.of(),Tail.EXACT,t,e,Layer.NORMAL);
      var gen=new org.opentaint.dataflow.bidi.store.Record(genOwner,Direction.FORWARD,ap.getZero(),retFact);
      f.getRecords().add(gen);
      var retPattern=f.pattern(ret,List.of(),Tail.EXACT,t,e);
      var views=gen.reversedAt(retPattern).iterator();
      check(views.hasNext(),"normal GEN record has an ordinary reverse view");
      var view=views.next();
      var backwardOut=new CollectingOut();
      ops.applyRecordLeaf(retFact,view,false,modeB,backwardOut,ap.getZero());
      check(backwardOut.getResults().size()==1 && backwardOut.getResults().get(0) instanceof Reach,
            "reverse GEN record returns ZERO, without an actual source callback");
      var replayOut=new CollectingOut();
      ops.applySummary(Reach.NORMAL,ap.getZero(),retFact,modeF,replayOut,ap.getZero());
      check(replayOut.getResults().size()==1,"forward saved GEN replay supplies result without callee initial");
      check(replayOut.getResults().get(0).getLayer()==Layer.NORMAL,"forward GEN replay retains NORMAL");
      System.out.println("{\"status\":\"PASS\",\"scope\":\"production AP primitives, not Target runtime\",\"mayActual\":\"DEMAND\",\"C2Initial\":\"EXACT\",\"calleeSinkFact\":\"NORMAL\",\"currentRouteAdmitted\":true,\"ordinaryWrapperRecordAnswersZero\":false,\"reverseNormalGENRecordReturnsZero\":true,\"savedForwardGENNeedsNewSourceHit\":false,\"fieldLimit2CallInput\":\"DEMAND\",\"fieldLimit4CallInput\":\"NORMAL\",\"controlZeroTriggersLocalGEN\":false}");
    }
  }
}
