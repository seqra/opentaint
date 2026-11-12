import java.util.*;
import org.opentaint.dataflow.bidi.ap.MarkSet;

/** Proof-side target-bucket prototype using the actual native immutable MarkSet.
 * No production caller directory, queue, analyzer or project is run. */
public final class CallerPackingMarkSetControl {
    static int assertions;
    static void require(boolean ok, String why) {
        assertions++;
        if (!ok) throw new AssertionError(why);
    }
    static long pair(int input, int output) { return ((long)input << 32) | (output & 0xffffffffL); }
    static MarkSet one(int mark) { return new MarkSet(new int[]{mark}); }
    static boolean member(MarkSet marks, int mark) {
        return Arrays.binarySearch(marks.getIds(),mark) >= 0;
    }
    static final class Relation {
        MarkSet diagonal = new MarkSet(new int[0]);
        final Map<Integer,MarkSet> changingByTarget = new HashMap<>();
        boolean add(int input, int output) {
            if (input == output) {
                boolean fresh = !member(diagonal,input);
                diagonal = diagonal.plus(one(input));
                return fresh;
            }
            MarkSet old = changingByTarget.getOrDefault(output,new MarkSet(new int[0]));
            boolean fresh = !member(old,input);
            changingByTarget.put(output,old.plus(one(input)));
            return fresh;
        }
        Set<Long> decode() {
            Set<Long> out = new HashSet<>();
            for (int m : diagonal.getIds()) out.add(pair(m,m));
            for (var bucket : changingByTarget.entrySet())
                for (int input : bucket.getValue().getIds()) out.add(pair(input,bucket.getKey()));
            return out;
        }
        Set<Integer> sourcesFor(int output) {
            Set<Integer> out = new HashSet<>();
            if (member(diagonal,output)) out.add(output);
            for (int input : changingByTarget.getOrDefault(output,new MarkSet(new int[0])).getIds())
                out.add(input);
            return out;
        }
    }
    public static void main(String[] args) {
        // Every relation over three opaque full IDs, including all mixed cases.
        for (int bits=0; bits < (1<<9); bits++) {
            Set<Long> scalar = new HashSet<>();
            Relation packed = new Relation(), reversed = new Relation();
            for (int n=0;n<9;n++) if ((bits & (1<<n))!=0) {
                int input=1+n/3, output=1+n%3;
                boolean fresh=scalar.add(pair(input,output));
                require(packed.add(input,output)==fresh,"Exact fresh pair admission");
                require(!packed.add(input,output),"Repeated pair must be duplicate");
            }
            for (int n=8;n>=0;n--) if ((bits & (1<<n))!=0) reversed.add(1+n/3,1+n%3);
            require(packed.decode().equals(scalar),"Exact scalar decode");
            require(reversed.decode().equals(scalar),"Arrival order membership equality");
            for (var bucket : packed.changingByTarget.entrySet())
                require(!member(bucket.getValue(),bucket.getKey()),"Diagonal must stay outside changing buckets");
            for (int output=1;output<=3;output++) {
                Set<Integer> expected=new HashSet<>();
                for (int input=1;input<=3;input++)
                    if (scalar.contains(pair(input,output))) expected.add(input);
                require(packed.sourcesFor(output).equals(expected),"Exact publication target selection");
            }
        }
        Relation sparse=new Relation();
        sparse.add(1,2); sparse.add(3,4);
        require(!sparse.decode().contains(pair(1,4)) && !sparse.decode().contains(pair(3,2)),
            "Pair buckets must not create a Cartesian product");
        MarkSet saved=sparse.changingByTarget.get(2);
        sparse.add(3,2);
        require(Arrays.equals(saved.getIds(),new int[]{1}),"Native MarkSet snapshots stay immutable");
        require(sparse.sourcesFor(2).equals(Set.of(1,3)),"Late growth adds the real source");
        sparse.add(1,1);
        require(sparse.decode().contains(pair(1,1)) && sparse.decode().contains(pair(1,2)),
            "Diagonal and changing memberships coexist");
        int[] exposed=sparse.diagonal.getIds(); exposed[0]=999;
        require(member(sparse.diagonal,1),"Public MarkSet arrays cannot mutate storage");
        System.out.println("PASS_CALLER_MARK_SET_CONTROL relations=512 assertions="+assertions+
            " engineRuns=0 projectScans=0 directoryRewritten=false");
    }
}
