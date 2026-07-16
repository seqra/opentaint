package test.samples;

import java.util.function.Supplier;

public class BaseOnlyMixedFuzzSample {
    private static String source() { return "tainted"; }
    private static void sink(String value) { }
    private static String identity(String value) { return value; }
    private static Box identityBox(Box box) { return box; }
    private static void store(Box box, String value) { box.setValue(value); }
    private static void touch(Box box) { box.setTag("touched"); }
    private static void forwardToSink(String value) { sink(value); }

    public static void directSetterThenTag() {
        Box b = new Box(); b.setValue(source()); b.setTag("x"); sink(b.getValue());
    }
    public static void sourceInLocal() {
        String value = source(); Box b = new Box(); b.setValue(value); b.setTag("x"); sink(b.getValue());
    }
    public static void identityBeforeStore() {
        Box b = new Box(); b.setValue(identity(source())); b.setTag("x"); sink(b.getValue());
    }
    public static void identityAfterLoad() {
        Box b = new Box(); b.setValue(source()); b.setTag("x"); sink(identity(b.getValue()));
    }
    public static void aliasBeforeStore() {
        Box b = new Box(); Box alias = b; alias.setValue(source()); b.setTag("x"); sink(alias.getValue());
    }
    public static void aliasBeforeMutation() {
        Box b = new Box(); b.setValue(source()); Box alias = b; alias.setTag("x"); sink(b.getValue());
    }
    public static void aliasBeforeLoad() {
        Box b = new Box(); b.setValue(source()); b.setTag("x"); Box alias = b; sink(alias.getValue());
    }
    public static void helperStore() {
        Box b = new Box(); store(b, source()); b.setTag("x"); sink(b.getValue());
    }
    public static void helperMutation() {
        Box b = new Box(); b.setValue(source()); touch(b); sink(b.getValue());
    }
    public static void helperSink() {
        Box b = new Box(); b.setValue(source()); b.setTag("x"); forwardToSink(b.getValue());
    }
    public static void boxIdentityBeforeStore() {
        Box b = identityBox(new Box()); b.setValue(source()); b.setTag("x"); sink(b.getValue());
    }
    public static void boxIdentityBeforeLoad() {
        Box b = new Box(); b.setValue(source()); b.setTag("x"); sink(identityBox(b).getValue());
    }

    public static void fluentStore() {
        Box b = new Box().withValue(source()); b.setTag("x"); sink(b.getValue());
    }
    public static void fluentMutation() {
        Box b = new Box(); b.setValue(source()); b.withTag("x"); sink(b.getValue());
    }
    public static void fluentChain() {
        Box b = new Box().withValue(source()).withTag("x"); sink(b.getValue());
    }
    public static void fluentLoad() {
        Box b = new Box(); b.setValue(source()); sink(b.withTag("x").getValue());
    }

    public static void doWhileMutation() {
        Box b = new Box(); b.setValue(source()); int i = 0; do { b.setTag("x"); } while (++i < 1); sink(b.getValue());
    }
    public static void tryFinallyMutation() {
        Box b = new Box(); b.setValue(source()); try { b.setTag("x"); } finally { b.setCount(1); } sink(b.getValue());
    }
    public static void switchMutation() {
        Box b = new Box(); b.setValue(source()); switch (b.hashCode() & 0) { case 0: b.setTag("x"); break; default: b.setCount(1); } sink(b.getValue());
    }

    public static void twoUnrelatedMutations() {
        Box b = new Box(); b.setValue(source()); b.setTag("x"); b.setCount(1); sink(b.getValue());
    }
    public static void primitiveMutation() {
        Box b = new Box(); b.setValue(source()); b.setCount(1); sink(b.getValue());
    }
    public static void objectMutation() {
        Box b = new Box(); b.setValue(source()); b.setOther(new Object()); sink(b.getValue());
    }
    public static void nullableMutation() {
        Box b = new Box(); b.setValue(source()); b.setOther(null); sink(b.getValue());
    }
    public static void inheritedMutation() {
        ChildBox b = new ChildBox(); b.setValue(source()); b.setTag("x"); sink(b.getValue());
    }
    public static void interfaceDispatchMutation() {
        Box b = new Box(); b.setValue(source()); Taggable taggable = b; taggable.setTag("x"); sink(b.getValue());
    }
    public static void supplierSource() {
        Supplier<String> supplier = BaseOnlyMixedFuzzSample::source; Box b = new Box(); b.setValue(supplier.get()); b.setTag("x"); sink(b.getValue());
    }

    public static void loadedIntoLocal() {
        Box b = new Box(); b.setValue(source()); b.setTag("x"); String value = b.getValue(); sink(value);
    }
    public static void loadedThroughTwoLocals() {
        Box b = new Box(); b.setValue(source()); b.setTag("x"); String first = b.getValue(); String second = first; sink(second);
    }
    public static void identityTwiceBeforeStore() {
        Box b = new Box(); b.setValue(identity(identity(source()))); b.setTag("x"); sink(b.getValue());
    }
    public static void identityTwiceAfterLoad() {
        Box b = new Box(); b.setValue(source()); b.setTag("x"); sink(identity(identity(b.getValue())));
    }
    public static void tagBeforeAndAfterStore() {
        Box b = new Box(); b.setTag("before"); b.setValue(source()); b.setTag("after"); sink(b.getValue());
    }
    public static void countBeforeTagAfterStore() {
        Box b = new Box(); b.setCount(0); b.setValue(source()); b.setTag("after"); sink(b.getValue());
    }
    public static void helperStoreAndMutation() {
        Box b = new Box(); store(b, source()); touch(b); sink(b.getValue());
    }
    public static void helperMutationTwice() {
        Box b = new Box(); b.setValue(source()); touch(b); touch(b); sink(b.getValue());
    }
    public static void fluentStoreHelperMutation() {
        Box b = new Box().withValue(source()); touch(b); sink(b.getValue());
    }
    public static void fluentMutationHelperSink() {
        Box b = new Box(); b.setValue(source()); b.withTag("x"); forwardToSink(b.getValue());
    }
    public static void twoBoxesFirstTainted() {
        Box first = new Box(); Box second = new Box(); first.setValue(source()); first.setTag("x"); second.setTag("y"); sink(first.getValue());
    }
    public static void twoBoxesSecondTainted() {
        Box first = new Box(); Box second = new Box(); second.setValue(source()); first.setTag("x"); second.setTag("y"); sink(second.getValue());
    }
    public static void synchronizedMutation() {
        Box b = new Box(); b.setValue(source()); synchronized (b) { b.setTag("x"); } sink(b.getValue());
    }
    public static void tryCatchMutation() {
        Box b = new Box(); b.setValue(source()); try { b.setTag("x"); } catch (RuntimeException ignored) { b.setCount(1); } sink(b.getValue());
    }
    public static void castBeforeLoad() {
        Box b = new ChildBox(); b.setValue(source()); b.setTag("x"); sink(((ChildBox) b).getValue());
    }
    private interface Taggable { void setTag(String tag); }

    private static class Box implements Taggable {
        private String value;
        private String tag;
        private int count;
        private Object other;
        void setValue(String value) { this.value = value; }
        String getValue() { return value; }
        @Override public void setTag(String tag) { this.tag = tag; }
        void setCount(int count) { this.count = count; }
        void setOther(Object other) { this.other = other; }
        Box withValue(String value) { this.value = value; return this; }
        Box withTag(String tag) { this.tag = tag; return this; }
    }

    private static final class ChildBox extends Box { }
}
