import java.lang.reflect.Constructor;
import java.util.*;
import kotlin.Pair;
import kotlin.sequences.SequencesKt;
import org.opentaint.dataflow.ap.ifds.AccessPathBase;
import org.opentaint.dataflow.ap.ifds.FieldAccessor;
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner;
import org.opentaint.dataflow.bidi.ap.*;
import org.opentaint.dataflow.bidi.store.RunSummaryStore;
import org.opentaint.dataflow.util.Cancellation;
import org.opentaint.dataflow.util.RefManager;

/** Existing-store inventory, without modifying the runtime or running an engine. */
public final class CurrentCompactionInventory {
    static final AccessPathBase P=AccessPathBase.Argument.Companion.create(0);
    static final AccessPathBase Q=AccessPathBase.Return.INSTANCE;
    static final ExclusionSet E=ExclusionSet.Empty.INSTANCE;
    static MarkSlot.Concrete T,U;
    static int f,checks;
    static void require(boolean ok,String message) {
        checks++; if (!ok) throw new AssertionError(message);
    }
    static ApManager manager() {
        return new ApManager(new Cancellation(),new RefManager(),
            new MarkTable(FrozenMarkDeclarations.Companion.getEMPTY()));
    }
    static Facts output(ApManager m,Tail tail,MarkSlot mark,List<Integer> path) {
        return m.factsOf(new PathFact(Q,path,tail,mark),E,Layer.DEMAND);
    }
    static List<Pair<PremiseKey,Facts>> rows(RunSummaryStore store) {
        return SequencesKt.toList(store.all());
    }
    public static void main(String[] args) throws Exception {
        Constructor<MarkSlot.Concrete> ctor=MarkSlot.Concrete.class.getDeclaredConstructor(int.class);
        ctor.setAccessible(true);T=ctor.newInstance(1);U=ctor.newInstance(2);
        f=new AccessorInterner().index(new FieldAccessor("OpaqueOwner","f","OpaqueType"));
        for (boolean reversed : new boolean[]{false,true}) {
            for (boolean backed : new boolean[]{false,true}) {
                ApManager m=manager();
                InitialAp premise=m.initial(new Pattern(new PathFact(P,List.of(),Tail.STAR,U),E));
                RunSummaryStore store=new RunSummaryStore(m,backed);
                Facts exact=output(m,Tail.EXACT,T,List.of(f)),may=output(m,Tail.ANY,T,List.of());
                store.addAdmittedAll(premise,reversed?may:exact);
                store.addAdmittedAll(premise,reversed?exact:may);
                require(rows(store).size()==1 && ((TaintTree)rows(store).get(0).getSecond()).getAnyTail()==Tail.ANY,
                    "Scalar same-premise MAY coverage is already implemented");
                System.out.println("EXISTING_SCALAR_MAY backed="+backed+" reversed="+reversed+" rows=1");
            }
            ApManager m=manager();
            InitialAp premise=m.initial(new Pattern(new PathFact(P,List.of(),Tail.STAR,T),E));
            RunSummaryStore store=new RunSummaryStore(m,true);
            Facts exact=output(m,Tail.EXACT,T,List.of(f)),may=output(m,Tail.ANY,T,List.of());
            store.addAdmittedAll(premise,reversed?may:exact);
            store.addAdmittedAll(premise,reversed?exact:may);
            require(rows(store).size()==2,"Diagonal MAY and scalar EXACT remain in separate lanes");
            System.out.println("RESIDUAL_CROSS_LANE_MAY reversed="+reversed+" rows=2");

            RunSummaryStore points=new RunSummaryStore(m,true);
            Facts rootExact=output(m,Tail.EXACT,T,List.of()),star=output(m,Tail.STAR,T,List.of());
            points.addAdmittedAll(premise,reversed?star:rootExact);
            points.addAdmittedAll(premise,reversed?rootExact:star);
            require(rows(points).size()==2,"DEMAND same-head STAR/EXACT still needs handoff equivalence");
            System.out.println("NEW_POINT_HANDOFF_EQUIVALENCE reversed="+reversed+" rows=2");
        }
        System.out.println("PASS_CURRENT_COMPACTION_INVENTORY checks="+checks+
            " engineRuns=0 projectScans=0 opaqueMarkIds=true");
    }
}
