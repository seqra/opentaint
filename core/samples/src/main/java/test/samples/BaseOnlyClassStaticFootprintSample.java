package test.samples;

public class BaseOnlyClassStaticFootprintSample {
    public static Object source() {
        return new Object();
    }

    public static void seed(Object value) {
    }

    public static void transition(Object value) {
    }

    public static void sink(Object value) {
    }

    private static void irrelevantLeaf() {
        Object ignored = new Object();
        ignored.toString();
    }

    private static void irrelevantWrapper() {
        irrelevantLeaf();
    }

    private static void relevantWrapper(Object value) {
        transition(value);
    }

    public static void transitiveRuleFootprint() {
        Object value = source();
        seed(value);
        irrelevantWrapper();
        relevantWrapper(value);
        sink(value);
    }
}
