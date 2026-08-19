package test.samples;

public class ObjectMethodDispatchSample {
    static class Value {
        @Override
        public int hashCode() {
            sink(source());
            return 0;
        }
    }

    public void callThroughObjectMustBeIgnored() {
        Object value = new Value();
        value.hashCode();
    }

    public void directOverrideCallRemainsAnalyzable() {
        Value value = new Value();
        value.hashCode();
    }

    public static String source() {
        return "tainted";
    }

    public static void sink(String value) {
    }
}
