package test.samples;

import java.lang.reflect.Method;

public class ReflectiveInvocationSample {

    public static String source() {
        return "tainted";
    }

    public static void sink(String value) {
    }

    public void leak(String value) {
        sink(value);
    }

    public void drop(String value) {
        sink("clean");
    }

    public static void directInvocationFlow() {
        ReflectiveInvocationSample receiver = new ReflectiveInvocationSample();
        receiver.leak(source());
    }

    public static void reflectiveLeakFlow() throws Exception {
        ReflectiveInvocationSample receiver = new ReflectiveInvocationSample();
        String name = "leak";
        Method method = ReflectiveInvocationSample.class.getMethod(name, String.class);
        method.invoke(receiver, source());
    }

    public static void reflectiveDropFlow() throws Exception {
        ReflectiveInvocationSample receiver = new ReflectiveInvocationSample();
        String name = "drop";
        Method method = ReflectiveInvocationSample.class.getMethod(name, String.class);
        method.invoke(receiver, source());
    }

    public static void reflectiveAmbiguousFlow(boolean flag) throws Exception {
        ReflectiveInvocationSample receiver = new ReflectiveInvocationSample();
        String name = flag ? "leak" : "drop";
        Method method = ReflectiveInvocationSample.class.getMethod(name, String.class);
        method.invoke(receiver, source());
    }

    public static void reflectiveUnresolvedFlow(String externalName) throws Exception {
        ReflectiveInvocationSample receiver = new ReflectiveInvocationSample();
        Method method = ReflectiveInvocationSample.class.getMethod(externalName, String.class);
        method.invoke(receiver, source());
    }

    public static int intSource() {
        return 1;
    }

    public static void intSink(int value) {
    }

    public void intLeak(int value) {
        intSink(value);
    }

    public static void reflectiveIntLeakFlow() throws Exception {
        ReflectiveInvocationSample receiver = new ReflectiveInvocationSample();
        String name = "intLeak";
        Method method = ReflectiveInvocationSample.class.getMethod(name, int.class);
        method.invoke(receiver, intSource());
    }

    public static void reflectiveDeclaredLeakFlow() throws Exception {
        ReflectiveInvocationSample receiver = new ReflectiveInvocationSample();
        Method method = ReflectiveInvocationSample.class.getDeclaredMethod("leak", String.class);
        method.invoke(receiver, source());
    }
}
