package test.samples;

public class BackwardPipelineSample {
    public static String source() {
        return "tainted";
    }

    public static void sinkA(String data) {
    }

    public static void sinkB(String data) {
    }

    public static void finish(String data) {
    }

    public static void finishState() {
    }

    public static String wrap(String data) {
        return data;
    }

    public static void sinkWrapped(String data) {
    }

    public void sharedMarkOneReached() {
        String data = source();
        sinkA(data);
        sinkB("constant");
    }

    public void sharedMarkBothReached() {
        String data = source();
        sinkA(data);
        sinkB(data);
    }

    public void localRequirementCleaned() {
        String data = source();
        sinkA(data);
        finish(data);
    }

    public void localRequirementCleanedInCallee() {
        String data = source();
        sinkA(data);
        finishData(data);
    }

    public void localRequirementKept() {
        String data = source();
        sinkA(data);
    }

    public void staticRequirementCleaned() {
        String data = source();
        sinkA(data);
        finishState();
    }

    public void staticRequirementCleanedInCallee() {
        String data = source();
        sinkInCallee(data);
        cleanup();
    }

    public void staticRequirementKept() {
        String data = source();
        sinkInCallee(data);
    }

    public void conditionalSourceInCallee() {
        String data = source();
        String wrapped = wrapInCallee(data);
        sinkWrapped(wrapped);
    }

    private String wrapInCallee(String data) {
        String wrapped = wrap(data);
        return wrapped;
    }

    private void finishData(String data) {
        finish(data);
    }

    private void sinkInCallee(String data) {
        sinkA(data);
    }

    private void cleanup() {
        finishState();
    }
}
