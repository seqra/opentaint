package test.samples;

import java.lang.reflect.Method;

public class DataFlowBenchReflectiveInvocationSample {

    public void leak(String value) {
        sink(value);
    }

    public void reflectiveInvocationFlow() throws Exception {
        DataFlowBenchReflectiveInvocationSample receiver = new DataFlowBenchReflectiveInvocationSample();
        String name = "leak";
        Method method = DataFlowBenchReflectiveInvocationSample.class.getMethod(name, String.class);
        method.invoke(receiver, source());
    }

    public void directInvocationFlow() {
        DataFlowBenchReflectiveInvocationSample receiver = new DataFlowBenchReflectiveInvocationSample();
        receiver.leak(source());
    }

    public String source() { return "tainted"; }

    public void sink(String data) { }
}
