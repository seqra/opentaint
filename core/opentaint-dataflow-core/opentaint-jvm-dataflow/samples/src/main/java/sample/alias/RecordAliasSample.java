package sample.alias;

public class RecordAliasSample {

    public record Payload(Object value) {}

    static void recordHashCodeInlined(Object src) {
        Payload payload = new Payload(src);
        payload.hashCode();
        sinkOneValue(payload.value());
    }

    static void sinkOneValue(Object value) {}
}
