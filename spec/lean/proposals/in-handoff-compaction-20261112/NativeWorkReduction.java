import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.List;
import org.opentaint.dataflow.ap.ifds.AccessPathBase;
import org.opentaint.dataflow.ap.ifds.FieldAccessor;
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner;
import org.opentaint.dataflow.bidi.ap.*;
import org.opentaint.dataflow.util.Cancellation;
import org.opentaint.dataflow.util.RefManager;

/** Native operator controls only; no trie rewrite, analyzer or project run. */
public final class NativeWorkReduction {
    static final AccessPathBase A = AccessPathBase.Argument.Companion.create(0);
    static final ExclusionSet E = ExclusionSet.Empty.INSTANCE;
    static int assertions;
    static void require(boolean condition, String message) {
        assertions++;
        if (!condition) throw new AssertionError(message);
    }
    static Pattern p(List<Integer> path, Tail tail, MarkSlot mark) {
        return new Pattern(new PathFact(A,path,tail,mark),E);
    }
    public static void main(String[] args) throws Exception {
        Constructor<MarkSlot.Concrete> constructor = MarkSlot.Concrete.class.getDeclaredConstructor(int.class);
        constructor.setAccessible(true);
        MarkSlot concrete = constructor.newInstance(1); // opaque identity; catalog lookup is not used
        MarkSlot flow = MarkSlot.Companion.getSTAR();
        AccessorInterner fields = new AccessorInterner();
        int f = fields.index(new FieldAccessor("OpaqueOwner","f","OpaqueType"));
        int g = fields.index(new FieldAccessor("OpaqueOwner","g","OpaqueType"));
        ApManager manager = new ApManager(new Cancellation(),new RefManager(),
            new MarkTable(FrozenMarkDeclarations.Companion.getEMPTY()));
        for (int run : new int[]{2,3,8}) {
            Direction direction = run % 2 == 0 ? Direction.BACKWARD : Direction.FORWARD;
            RestrictedInitialPolicy policy = new RestrictedInitialPolicy(run,7,direction,null);
            for (MarkSlot mark : new MarkSlot[]{flow,concrete}) {
                for (Layer layer : Layer.values()) {
                    for (Tail actualTail : new Tail[]{Tail.STAR,Tail.EXACT}) {
                        Pattern actual = p(List.of(f),actualTail,mark);
                        List<Pattern> demands = new ArrayList<>();
                        demands.add(p(List.of(),Tail.ANY,mark));
                        demands.add(p(List.of(f),Tail.ANY,mark));
                        demands.add(p(List.of(f),Tail.STAR,mark));
                        demands.add(p(List.of(f,g),Tail.ANY,mark));
                        demands.add(p(List.of(f,g),Tail.STAR,mark));
                        List<InitialEmission> before = new ArrayList<>(), after = new ArrayList<>();
                        for (Pattern demand : demands) {
                            var family = policy.emitAdmissions(demand,actual,layer);
                            before.addAll(family);
                            if (demand.getFact().getPath().size() > actual.getFact().getPath().size()) {
                                require(family.isEmpty(),"Strict descendant of STAR/EXACT must emit no companions");
                            } else after.addAll(family);
                            for (InitialEmission emitted : family) {
                                require(manager.initial(emitted.getPattern()).toPattern().equals(emitted.getPattern()),
                                    "Descriptor must survive native interning without geometry changes");
                            }
                        }
                        require(before.equals(after),"Pruning must preserve ordered complete families");
                    }
                }
            }
        }
        RestrictedInitialPolicy forward = new RestrictedInitialPolicy(7,6,Direction.FORWARD,null);
        for (Tail actual : new Tail[]{Tail.ANY,Tail.ANY_TAINT}) {
            require(!forward.emitAdmissions(p(List.of(f),Tail.EXACT,concrete),
                p(List.of(),actual,concrete),Layer.NORMAL).isEmpty(),"MAY/MUST child admission must remain enabled");
        }
        System.out.println("PASS_NATIVE_WORK_REDUCTION assertions="+assertions+
            " engineRuns=0 projectScans=0 exclusions=empty nativeTrieRewritten=false");
    }
}
