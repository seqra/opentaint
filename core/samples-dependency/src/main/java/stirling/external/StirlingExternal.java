package stirling.external;

public final class StirlingExternal {
    private StirlingExternal() { }

    public static final class FileInput { }

    public static final class PdfDocumentFactory {
        public PdfDocument load(FileInput input, boolean readOnly) { return null; }
    }

    public static final class PdfDocument {
        public DocumentInfo getDocumentInformation() { return null; }
    }

    public static final class DocumentInfo {
        public String getTitle() { return null; }
    }

    public static final class JsonMapper {
        public JsonNode createObjectNode() { return null; }
        public JsonWriter writerWithDefaultPrettyPrinter() { return null; }
    }

    public static final class JsonNode {
        public JsonNode put(String name, String value) { return this; }
        public JsonNode set(String name, JsonNode value) { return this; }
    }

    public static final class JsonWriter {
        public String writeValueAsString(JsonNode value) { return null; }
    }
}
