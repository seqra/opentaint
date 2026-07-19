package test.samples;

import org.springframework.http.MediaType;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;
import test.samples.stirling.common.StirlingWebResponseUtils;
import test.samples.stirling.model.StirlingPdfRequest;

@RestController
public class StirlingTraceResolutionRegressionSample {
    @GetMapping()
    @SuppressWarnings("rawtypes")
    public ResponseEntity getPdfInfo(StirlingPdfRequest request) {
        byte[] inputFile = request.getFileInput();
        return StirlingWebResponseUtils.bytesToWebResponse(
                inputFile, "response.json", new MediaType());
    }
}
