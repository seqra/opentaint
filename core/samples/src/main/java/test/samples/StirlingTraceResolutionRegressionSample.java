package test.samples;

import java.nio.charset.StandardCharsets;

import org.springframework.http.MediaType;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.ModelAttribute;
import org.springframework.web.bind.annotation.RestController;

import stirling.external.StirlingExternal.DocumentInfo;
import stirling.external.StirlingExternal.FileInput;
import stirling.external.StirlingExternal.JsonMapper;
import stirling.external.StirlingExternal.JsonNode;
import stirling.external.StirlingExternal.PdfDocument;
import stirling.external.StirlingExternal.PdfDocumentFactory;
import test.samples.stirling.common.StirlingWebResponseUtils;

/**
 * Reduction of the Stirling flow:
 * request -> JSON bytes -> WebResponseUtils.bytesToWebResponse -> ResponseEntity.Body -> return.
 */
@RestController
public final class StirlingTraceResolutionRegressionSample {
    private PdfDocumentFactory pdfDocumentFactory;

    @GetMapping
    public ResponseEntity<byte[]> cleanResponse() {
        return StirlingWebResponseUtils.bytesToWebResponse(
                new byte[0], "empty.json", MediaType.APPLICATION_JSON);
    }

    @GetMapping
    public ResponseEntity<byte[]> getPdfInfo(@ModelAttribute Request request) {
        PdfDocument document = pdfDocumentFactory.load(request.getFileInput(), true);
        DocumentInfo info = document.getDocumentInformation();
        JsonMapper mapper = new JsonMapper();
        JsonNode jsonOutput = mapper.createObjectNode();
        JsonNode metadata = mapper.createObjectNode();
        metadata.put("Title", info.getTitle());
        jsonOutput.set("Metadata", metadata);
        String jsonString = mapper.writerWithDefaultPrettyPrinter().writeValueAsString(jsonOutput);
        return StirlingWebResponseUtils.bytesToWebResponse(
                jsonString.getBytes(StandardCharsets.UTF_8),
                "response.json",
                MediaType.APPLICATION_JSON);
    }

    public static final class Request {
        private FileInput fileInput;

        public FileInput getFileInput() {
            return fileInput;
        }
    }
}
