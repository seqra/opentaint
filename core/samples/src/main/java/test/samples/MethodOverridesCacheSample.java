package test.samples;

public class MethodOverridesCacheSample {
    public static class Root {
        public String value() {
            return "clean";
        }
    }

    public static class Left extends Root {
    }

    public static class Right extends Root {
        @Override
        public String value() {
            return source();
        }
    }

    public void narrowCallMustNotReuseBroadOverrides(Root broad, Left left) {
        broad.value();
        sink(left.value());
    }

    public static String source() {
        return "tainted";
    }

    public static void sink(String value) {
    }
}
