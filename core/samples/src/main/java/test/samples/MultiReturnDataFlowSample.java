package test.samples;

public class MultiReturnDataFlowSample {

    public void allReturnsTaintedFlow(int mode) {
        String data = source();
        sink(pickAlwaysTainted(mode, data));
    }

    private String pickAlwaysTainted(int mode, String data) {
        if (mode == 0) {
            return data;
        }
        if (mode == 1) {
            return data + "!";
        }
        return data;
    }

    public void oneReturnTaintedFlow(int mode) {
        String data = source();
        sink(pickOneTainted(mode, data));
    }

    private String pickOneTainted(int mode, String data) {
        if (mode == 0) {
            return "first";
        }
        if (mode == 1) {
            return data;
        }
        return "last";
    }

    public void noReturnTaintedFlow(int mode) {
        String data = source();
        sink(discardTaint(mode, data));
    }

    private String discardTaint(int mode, String data) {
        String local = data;
        if (mode == 0) {
            return "first";
        }
        if (mode == 1) {
            return "middle";
        }
        return "last";
    }

    public void taintNotReturnedFlow() {
        sink(createAndDiscard());
    }

    private String createAndDiscard() {
        String data = source();
        if (data.isEmpty()) {
            return "empty";
        }
        return "done";
    }

    public void earlyReturnGuardFlow(String input) {
        String data = source();
        sink(guard(input, data));
    }

    private String guard(String input, String data) {
        if (input == null) {
            return "";
        }
        return data;
    }

    public void nestedMultiReturnFlow(int mode) {
        String data = source();
        sink(outer(mode, data));
    }

    private String outer(int mode, String data) {
        if (mode == 0) {
            return inner(mode, data);
        }
        if (mode == 1) {
            return "outer";
        }
        return inner(mode + 1, data);
    }

    private String inner(int mode, String data) {
        if (mode > 5) {
            return "inner";
        }
        return data;
    }

    public void chainedMultiReturnFlow(int mode) {
        String data = source();
        String first = pickOneTainted(mode, data);
        sink(pickAlwaysTainted(mode, first));
    }

    public void loopReturnFlow(int count) {
        String data = source();
        sink(firstMatch(count, data));
    }

    private String firstMatch(int count, String data) {
        for (int i = 0; i < count; i++) {
            if (i == 3) {
                return data;
            }
        }
        return "none";
    }

    public void returnOrThrowFlow(int mode) {
        String data = source();
        sink(pickOrThrow(mode, data));
    }

    private String pickOrThrow(int mode, String data) {
        if (mode < 0) {
            throw new IllegalArgumentException("bad mode");
        }
        if (mode == 0) {
            return data;
        }
        return "clean";
    }

    public void taintArgumentThenReturnFlow() {
        Box box = new Box();
        taintThenReturn(box);
        sink(box.value);
    }

    private void taintThenReturn(Box box) {
        box.value = source();
    }

    public void taintArgumentThenThrowFlow() {
        Box box = new Box();
        try {
            taintThenAlwaysThrow(box);
        } catch (IllegalStateException e) {
            // expected
        }
        sink(box.value);
    }

    private void taintThenAlwaysThrow(Box box) {
        box.value = source();
        throw new IllegalStateException("boom");
    }

    public static class Box {
        public String value;
    }

    public String source() { return "tainted"; }
    public void sink(String data) { }
}
