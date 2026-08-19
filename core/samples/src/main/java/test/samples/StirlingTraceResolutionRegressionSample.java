package test.samples;

import java.io.IOException;
import java.nio.charset.StandardCharsets;

import org.springframework.http.MediaType;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.ModelAttribute;
import org.springframework.web.bind.annotation.RestController;

import stirling.external.StirlingExternal.FileInput;
import stirling.external.StirlingExternal.JsonMapper;
import stirling.external.StirlingExternal.JsonNode;
import stirling.external.StirlingExternal.PdfDocumentFactory;
import test.samples.StirlingTraceResolutionRegressionPolluter.ApplicationProperties;
import test.samples.stirling.common.StirlingWebResponseUtils;

/**
 * Reduction of the Stirling flow:
 * Spring component state -> JSON bytes -> WebResponseUtils.bytesToWebResponse
 * -> ResponseEntity.Body -> return.
 */
@RestController
public final class StirlingTraceResolutionRegressionSample {
    private final PdfDocumentFactory pdfDocumentFactory;
    private final ApplicationProperties applicationProperties;

    public StirlingTraceResolutionRegressionSample(
            PdfDocumentFactory pdfDocumentFactory,
            ApplicationProperties applicationProperties) {
        this.pdfDocumentFactory = pdfDocumentFactory;
        this.applicationProperties = applicationProperties;
    }

    @GetMapping
    public ResponseEntity<byte[]> getPdfInfo(@ModelAttribute Request request) throws IOException {
        FileInput inputFile = request.getFileInput();
        pdfDocumentFactory.load(inputFile, true);
        JsonMapper mapper = new JsonMapper();
        JsonNode jsonOutput = mapper.createObjectNode();
        JsonNode metadata = mapper.createObjectNode();
        metadata.put("Title", applicationProperties.getValue());
        jsonOutput.set("Metadata", metadata);
        JsonNode basicInfo = mapper.createObjectNode();
        String fileSizeInBytes = inputFile.getSize();
        basicInfo.put("FileSizeInBytes", fileSizeInBytes);
        jsonOutput.set("BasicInfo", basicInfo);
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
