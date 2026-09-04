package test.samples;

public class OverApproximateStartTraceSample {
    public static String source() {
        return "source";
    }

    public static void sink(String value) {
    }

    private static String identity(String value) {
        return value;
    }

    private static String sourceOnEitherBranch(boolean firstBranch) {
        String value;
        if (firstBranch) {
            value = source();
        } else {
            value = source();
        }
        return identity(value);
    }

    public static void nonZeroSummary() {
        String value = source();
        sink(identity(value));
    }

    public static void zeroSummary(boolean firstBranch) {
        sink(sourceOnEitherBranch(firstBranch));
    }
}
