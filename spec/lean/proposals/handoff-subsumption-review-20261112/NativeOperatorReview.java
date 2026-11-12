import java.lang.reflect.Constructor;
import java.util.List;
import org.opentaint.dataflow.ap.ifds.AccessPathBase;
import org.opentaint.dataflow.ap.ifds.FieldAccessor;
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner;
import org.opentaint.dataflow.bidi.ap.*;

/** Isolated native operator checks. No engine, project scan or store mutation. */
public final class NativeOperatorReview {
    private static final ExclusionSet E = ExclusionSet.Empty.INSTANCE;
    private static final AccessPathBase A = AccessPathBase.Argument.Companion.create(0);
    private static final AccessPathBase RET = AccessPathBase.Return.INSTANCE;
    private static MarkSlot.Concrete T;

    private static Pattern pattern(AccessPathBase base, List<Integer> path, Tail tail) {
        return new Pattern(new PathFact(base, path, tail, T), E);
    }
    private static void require(boolean value, String message) {
        if (!value) throw new AssertionError(message);
    }
    public static void main(String[] args) throws Exception {
        Constructor<MarkSlot.Concrete> constructor = MarkSlot.Concrete.class.getDeclaredConstructor(int.class);
        constructor.setAccessible(true);
        T = constructor.newInstance(1); // Opaque full mark; no catalog/group operation is used.
        int f = new AccessorInterner().index(new FieldAccessor("OpaqueOwner", "f", "OpaqueType"));

        PathFact input = pattern(A, List.of(), Tail.STAR).getFact();
        PathEdge x = new PathEdge(input, pattern(RET, List.of(), Tail.EXACT).getFact(), E, E, E);
        PathEdge y = new PathEdge(input, pattern(RET, List.of(), Tail.STAR).getFact(), E, E, E);
        Conclusion actual = new Conclusion(pattern(A, List.of(f), Tail.EXACT).getFact(), E, false);
        Conclusion rx = ((EdgeOutcome.Fact) ReferenceKt.concat(actual, x, true, false, true, false)).getConclusion();
        Conclusion ry = ((EdgeOutcome.Fact) ReferenceKt.concat(actual, y, true, false, true, false)).getConclusion();
        require(rx.getFact().getPath().isEmpty() && rx.getFact().getTail() == Tail.EXACT && rx.getDemand(), "EXACT output must be at ret root, DEMAND");
        require(ry.getFact().getPath().equals(List.of(f)) && ry.getFact().getTail() == Tail.EXACT && ry.getDemand(), "STAR output must carry f, DEMAND");
        require(!rx.equals(ry), "Demand query equivalence must not be read as raw transfer equality");
        System.out.println("B2_RAW_TRANSFER X=" + rx + " Y=" + ry);

        RestrictedInitialPolicy policy = new RestrictedInitialPolicy(6, 5, Direction.BACKWARD, null);
        Pattern offeredReturn = pattern(RET, List.of(), Tail.STAR);
        var bx = policy.emitAdmissions(pattern(RET, List.of(), Tail.STAR), offeredReturn, Layer.DEMAND);
        var by = policy.emitAdmissions(pattern(RET, List.of(), Tail.EXACT), offeredReturn, Layer.DEMAND);
        require(bx.equals(by) && bx.size() == 1 && bx.get(0).getPattern().getFact().getTail() == Tail.EXACT,
                "B2 late C2 point families must agree");
        System.out.println("B2_C2_EQUAL " + bx);

        Pattern pointEntry = pattern(A, List.of(f), Tail.EXACT);
        Pattern mayEntry = pattern(A, List.of(), Tail.ANY);
        Pattern offeredChild = pattern(A, List.of(f), Tail.STAR);
        var pointFamily = policy.emitAdmissions(pointEntry, offeredChild, Layer.DEMAND);
        var mayFamily = policy.emitAdmissions(mayEntry, offeredChild, Layer.DEMAND);
        require(pointFamily.size() == 1 && pointFamily.get(0).getPattern().equals(pointEntry), "Point entry must keep exact child initial");
        require(mayFamily.stream().noneMatch(i -> i.getPattern().equals(pointEntry)), "Ancestor MAY family has no concrete exact child initial in this cell");
        require(policy.canStoreInitial(pointEntry, pointEntry) && policy.canStoreInitial(mayEntry, pointEntry),
                "Both C5 entries must accept the exact stored child");
        System.out.println("C1_C2_DIFFERENT point=" + pointFamily + " ancestorMAY=" + mayFamily);
        System.out.println("C1_C5_POINT_ADMITTED_BY_BOTH true");

        Pattern rootPoint = pattern(A, List.of(), Tail.EXACT);
        boolean strong = ReferenceKt.satisfies(pattern(A, List.of(), Tail.ANY_TAINT), rootPoint, false, SummaryReadRole.CURRENT);
        boolean weak = ReferenceKt.satisfies(pattern(A, List.of(), Tail.STAR), rootPoint, false, SummaryReadRole.CURRENT);
        require(!strong && weak, "B1 raw MUST and STAR premises are not equivalent on an exact input");
        System.out.println("B1_RAW_PREMISE exactActual: MUST=" + strong + " STAR=" + weak);
        require(ReferenceKt.startFact(pattern(A, List.of(), Tail.STAR)).getDemand(), "Concrete STAR initial is DEMAND");
        System.out.println("PASS_NATIVE_OPERATOR_REVIEW engineRuns=0 findingNecessityProved=false");
    }
}
