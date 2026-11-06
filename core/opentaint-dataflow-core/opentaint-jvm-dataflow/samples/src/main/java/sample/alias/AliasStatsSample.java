package sample.alias;

/** Samples of the alias statistics tests (AliasShadowModeTest). */
public class AliasStatsSample {

    static class Box {
        Object value;
    }

    /** The read of a field that no statement wrote: the answer path holds only a null-valued origin. */
    static void readOfUnwrittenField() {
        Box x = new Box();
        Object a = x.value;
        probe(a, x);
    }

    /** The read of a written field: the answer paths share the argument with the read value. */
    static void readOfWrittenField(Object v) {
        Box x = new Box();
        x.value = v;
        Object b = x.value;
        probe(b, x);
    }

    static void probe(Object a, Object b) {
    }
}
