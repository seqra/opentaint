package test.samples;

public class FieldFlowSample {
    private static class ClassWithField {
        String field;
    }

    public void fieldWriteFlow() {
        String data = source();
        ClassWithField cls = new ClassWithField();

        cls.field = data;
        sink(cls.field);
    }

    public void fieldReadKillFlow() {
        ClassWithField cls = new ClassWithField();
        String data = source();
        data = cls.field;
        sink(data);
    }

    public void mayAliasFieldWriteFlow(boolean flag) {
        ClassWithField safe = new ClassWithField();
        ClassWithField tainted = new ClassWithField();
        tainted.field = source();

        ClassWithField alias = flag ? safe : tainted;
        safe.field = "safe";
        sink(alias.field);
    }

    public String source() { return "tainted"; }
    public void sink(String data) { }
}
