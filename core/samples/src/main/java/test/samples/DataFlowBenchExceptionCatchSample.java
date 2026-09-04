package test.samples;

public class DataFlowBenchExceptionCatchSample {

    static final class IntFlowException extends Exception {
        private static final long serialVersionUID = 1L;
        int value;
    }

    static final class StringFlowException extends Exception {
        private static final long serialVersionUID = 1L;
        String value;
    }

    public void exceptionCatchIntFlow() {
        try {
            IntFlowException flow = new IntFlowException();
            flow.value = intSource();
            throw flow;
        } catch (IntFlowException caught) {
            intSink(caught.value);
        }
    }

    public void exceptionCatchStringFlow() {
        try {
            StringFlowException flow = new StringFlowException();
            flow.value = source();
            throw flow;
        } catch (StringFlowException caught) {
            sink(caught.value);
        }
    }

    public void carrierFieldFlow() {
        StringFlowException flow = new StringFlowException();
        flow.value = source();
        sink(flow.value);
    }

    public int intSource() { return 1; }

    public void intSink(int data) { }

    public String source() { return "tainted"; }

    public void sink(String data) { }
}
