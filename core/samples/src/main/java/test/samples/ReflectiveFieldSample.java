package test.samples;

import java.lang.reflect.Field;

public class ReflectiveFieldSample {

    public static class Holder {
        public String tainted;
        public String clean;
    }

    public static String source() {
        return "tainted";
    }

    public static void sink(String value) {
    }

    public static void directFieldFlow() {
        Holder holder = new Holder();
        holder.tainted = source();
        sink(holder.tainted);
    }

    public static void reflectiveSameFieldFlow() throws Exception {
        Holder holder = new Holder();
        Field written = Holder.class.getDeclaredField("tainted");
        written.set(holder, source());
        Field read = Holder.class.getDeclaredField("tainted");
        sink((String) read.get(holder));
    }

    public static void reflectiveOtherFieldFlow() throws Exception {
        Holder holder = new Holder();
        Field written = Holder.class.getDeclaredField("tainted");
        written.set(holder, source());
        Field read = Holder.class.getDeclaredField("clean");
        sink((String) read.get(holder));
    }

    public static class IntHolder {
        public int tainted;
        public int clean;
    }

    public static int intSource() {
        return 1;
    }

    public static void intSink(int value) {
    }

    public static void reflectiveIntSameFieldFlow() throws Exception {
        IntHolder holder = new IntHolder();
        Field written = IntHolder.class.getDeclaredField("tainted");
        written.setInt(holder, intSource());
        Field read = IntHolder.class.getDeclaredField("tainted");
        intSink(read.getInt(holder));
    }

    public static void reflectiveIntOtherFieldFlow() throws Exception {
        IntHolder holder = new IntHolder();
        Field written = IntHolder.class.getDeclaredField("tainted");
        written.setInt(holder, intSource());
        Field read = IntHolder.class.getDeclaredField("clean");
        intSink(read.getInt(holder));
    }

    public static void reflectiveUnresolvedFieldFlow(String externalName) throws Exception {
        Holder holder = new Holder();
        Field written = Holder.class.getDeclaredField(externalName);
        written.set(holder, source());
        Field read = Holder.class.getDeclaredField("clean");
        sink((String) read.get(holder));
    }
}
