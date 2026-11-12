import java.lang.reflect.Constructor;
import java.util.List;
import org.opentaint.dataflow.ap.ifds.AccessPathBase;
import org.opentaint.dataflow.ap.ifds.FieldAccessor;
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner;
import org.opentaint.dataflow.bidi.ap.*;

/** Check demand-specific coverage cells, without a project or engine run. */
public final class DemandCoverageReview {
    static final ExclusionSet E = ExclusionSet.Empty.INSTANCE;
    static final AccessPathBase A = AccessPathBase.Argument.Companion.create(0);
    static MarkSlot.Concrete T;
    static Pattern p(List<Integer> path, Tail tail) {
        return new Pattern(new PathFact(A,path,tail,T),E);
    }
    static void require(boolean value, String why) {
        if (!value) throw new AssertionError(why);
    }
    public static void main(String[] args) throws Exception {
        Constructor<MarkSlot.Concrete> constructor = MarkSlot.Concrete.class.getDeclaredConstructor(int.class);
        constructor.setAccessible(true); T = constructor.newInstance(1);
        AccessorInterner fields = new AccessorInterner();
        int f=fields.index(new FieldAccessor("OpaqueOwner","f","OpaqueType"));
        int g=fields.index(new FieldAccessor("OpaqueOwner","g","OpaqueType"));
        RestrictedInitialPolicy policy = new RestrictedInitialPolicy(6,5,Direction.BACKWARD,null);

        Pattern exactF=p(List.of(f),Tail.EXACT), exactFG=p(List.of(f,g),Tail.EXACT);
        Pattern rootStar=p(List.of(),Tail.STAR), rootMay=p(List.of(),Tail.ANY);
        var point=policy.emitAdmissions(exactF,exactF,Layer.NORMAL);
        var samePoint=policy.emitAdmissions(p(List.of(f),Tail.STAR),exactF,Layer.NORMAL);
        require(point.equals(samePoint),"Same-head concrete STAR/EXACT demands must agree");
        require(policy.emitAdmissions(rootStar,exactF,Layer.NORMAL).isEmpty(),"Ancestor STAR does not admit the deeper exact point");
        System.out.println("STAR_ANCESTOR_IS_NOT_DEMAND_COVER exactF="+point+" rootStar=[]");

        var mayF=policy.emitAdmissions(rootMay,exactF,Layer.NORMAL);
        require(mayF.containsAll(point),"Ancestor MAY must reproduce the first-field exact start for this precise offer");
        System.out.println("MAY_FIRST_FIELD_PRECISE_OFFER_COVERS_POINT "+mayF);

        var deepPoint=policy.emitAdmissions(exactFG,exactFG,Layer.NORMAL);
        var deepMay=policy.emitAdmissions(rootMay,exactFG,Layer.NORMAL);
        require(deepPoint.size()==1 && deepPoint.get(0).getPattern().equals(exactFG),"Point request keeps the deep exact initial");
        require(deepMay.stream().noneMatch(i->i.getPattern().equals(exactFG)),"MAY retains only the first field at this step");
        require(!policy.canStoreInitial(rootMay,exactFG),"Current C5 image is first-field bounded too");
        System.out.println("MAY_DEEP_POINT_NEEDS_SIMULATION exact="+deepPoint+" may="+deepMay);

        Pattern mustF=p(List.of(f),Tail.ANY_TAINT);
        RestrictedInitialPolicy forward = new RestrictedInitialPolicy(7,6,Direction.FORWARD,null);
        var uniformPoint=forward.emitAdmissions(exactF,mustF,Layer.NORMAL);
        var uniformMay=forward.emitAdmissions(rootMay,mustF,Layer.NORMAL);
        require(uniformPoint.get(0).getLayer()==Layer.NORMAL && uniformPoint.get(0).getPattern().equals(exactF),"Point request has a NORMAL exact result for uniform actual");
        require(uniformMay.get(0).getLayer()==Layer.DEMAND && uniformMay.get(0).getPattern().getFact().getTail()==Tail.STAR,"MAY first-field result is concrete STAR/DEMAND here");
        System.out.println("MAY_UNIFORM_ACTUAL_LAYER_DIFFERENCE exact="+uniformPoint+" may="+uniformMay);

        Pattern coarse=p(List.of(),Tail.ANY);
        var coarsePoint=policy.emitAdmissions(exactF,coarse,Layer.DEMAND);
        var coarseMay=policy.emitAdmissions(rootMay,coarse,Layer.DEMAND);
        require(coarsePoint.get(0).getPattern().equals(exactF),"Concrete point demand can start provisionally at f");
        require(coarseMay.stream().noneMatch(i->i.getPattern().equals(exactF)),"MAY root start does not itself enumerate f");
        System.out.println("MAY_COARSE_ACTUAL_NEEDS_SIMULATION exact="+coarsePoint+" may="+coarseMay);
        System.out.println("PASS_DEMAND_COVERAGE_REVIEW engineRuns=0 lostSinkProved=false");
    }
}
