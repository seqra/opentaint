package test.samples;

public class PrescanInitializationSample {
    private interface Runner {
        void run(String value);
    }

    private static final Runner STATIC_RUNNER = PrescanInitializationSample::sink;

    private final Runner instanceRunner;

    private PrescanInitializationSample() {
        instanceRunner = PrescanInitializationSample::sink;
    }

    public static String source() {
        return "tainted";
    }

    public static void sink(String value) {
        // test sink
    }

    public static void staticEntry() {
        STATIC_RUNNER.run(source());
    }

    public void instanceEntry() {
        instanceRunner.run(source());
    }

    private static void unreachablePrivateFlow() {
        sink(source());
    }

    public static void safeEntry() {
        sink("safe");
    }
}
