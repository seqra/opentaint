package test.samples;

public class BackwardCallSample {
    public void directCall() {
        sink(source());
    }

    public void noSourceCall() {
        String data = source();
        sink(safe());
    }

    public void libraryConcat() {
        String data = source();
        sink(data.concat("suffix"));
    }

    public void libraryStringBuilder() {
        String data = source();
        StringBuilder sb = new StringBuilder();
        sb.append(data);
        sink(sb.toString());
    }

    public void libraryStringBuilderOtherValue() {
        String data = source();
        StringBuilder sb = new StringBuilder();
        sb.append(safe());
        sink(sb.toString());
    }

    public void calleeArgHeapEffect() {
        StringBuilder sb = new StringBuilder();
        fill(sb);
        sink(sb.toString());
    }

    public void calleeArgHeapEffectOtherArg() {
        StringBuilder sb = new StringBuilder();
        StringBuilder other = new StringBuilder();
        fill(other);
        sink(sb.toString());
    }

    public void calleeReturnValue() {
        String data = identity(source());
        sink(data);
    }

    public void cleanedArgument() {
        String data = source();
        sanitize(data);
        sink(data);
    }

    public void cleanedResult() {
        String data = source();
        sink(data.trim());
    }

    public void libraryCopyMark() {
        String data = source();
        sink(data.strip());
    }

    public void conditionalSource() {
        String data = source();
        sink(transform(data));
    }

    private void fill(StringBuilder sb) {
        sb.append(source());
    }

    private String identity(String value) {
        return value;
    }

    public void sanitize(String data) { }

    public String transform(String data) { return data; }

    public String safe() { return "safe"; }

    public String source() { return "tainted"; }

    public void sink(String data) { }
}
