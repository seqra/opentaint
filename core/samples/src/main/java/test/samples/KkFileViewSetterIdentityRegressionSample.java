package test.samples;

public class KkFileViewSetterIdentityRegressionSample {
    private static String source() {
        return "untrusted";
    }

    private static void sink(String value) {
    }

    public static void taintedLocalSurvivesUnrelatedSetters() {
        String outFilePath = source();
        FileAttribute attribute = new FileAttribute();

        attribute.setOutFilePath(outFilePath);
        attribute.setType("finalized");

        sink(attribute.getOutFilePath());
    }

    private static final class FileAttribute {
        private String type;
        private String outFilePath;

        void setType(String type) {
            this.type = type;
        }

        void setOutFilePath(String outFilePath) {
            this.outFilePath = outFilePath;
        }

        String getOutFilePath() {
            return outFilePath;
        }
    }
}
