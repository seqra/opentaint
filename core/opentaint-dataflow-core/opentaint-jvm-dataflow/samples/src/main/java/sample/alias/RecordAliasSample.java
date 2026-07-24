package sample.alias;

// Records lower equals/hashCode/toString to an invokedynamic bootstrapped by
// java.lang.runtime.ObjectMethods.bootstrap, which declares 6 parameters while
// the dynamic call site supplies one (the record instance). When alias analysis
// inlines the record method and then its bootstrap, mapping the 6 parameters
// onto the single call argument reads arguments the call never provided. This
// sample reproduces exactly that shape so the arity guard in resolveCallNoCache
// can be pinned: without the guard the analysis crashes with
// "Incorrect argument idx"; with it the bootstrap call is treated as opaque.
public class RecordAliasSample {

    public record Payload(Object value) {}

    static void recordHashCodeInlined(Object src) {
        Payload p = new Payload(src);
        // p.hashCode() is a record method whose body is the ObjectMethods
        // invokedynamic; alias analysis inlines it (and the bootstrap) at depth 2.
        p.hashCode();
        // echo is a local var so the test can query its aliases (which triggers
        // the full alias computation, and with it the record-method inlining).
        Object echo = p.value();
        sinkOneValue(echo);
    }

    static void sinkOneValue(Object v) { }
}
