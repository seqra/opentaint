package test.samples;

import org.springframework.http.MediaType;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;
import stirling.external.StirlingExternal.DocumentInfo;
import stirling.external.StirlingExternal.JsonMapper;
import stirling.external.StirlingExternal.JsonNode;
import stirling.external.StirlingExternal.PdfDocument;
import stirling.external.StirlingExternal.PdfDocumentFactory;
import test.samples.stirling.common.StirlingWebResponseUtils;
import test.samples.stirling.model.StirlingPdfRequest;

import java.nio.charset.StandardCharsets;

@RestController
public class StirlingTraceResolutionRegressionSample {
    private PdfDocumentFactory pdfDocumentFactory;

    @GetMapping()
    public ResponseEntity<byte[]> getPdfInfo(StirlingPdfRequest request) {
        PdfDocument document = pdfDocumentFactory.load(request.getFileInput(), true);
        DocumentInfo info = document.getDocumentInformation();
        JsonMapper objectMapper = new JsonMapper();
        JsonNode jsonOutput = objectMapper.createObjectNode();
        JsonNode metadata = objectMapper.createObjectNode();
        metadata.put("Title", info.getTitle());
        jsonOutput.set("Metadata", metadata);
        StringHolder holder = new StringHolder(
                objectMapper.writerWithDefaultPrettyPrinter().writeValueAsString(jsonOutput));
        String jsonString = holder.value;
        ResponseEntity<byte[]> response = StirlingWebResponseUtils.bytesToWebResponse(
                jsonString.getBytes(StandardCharsets.UTF_8), "response.json", MediaType.APPLICATION_JSON);
        return response;
    }

    private static final class StringHolder {
        private final String value;

        private StringHolder(String value) {
            this.value = value;
        }
    }
}
