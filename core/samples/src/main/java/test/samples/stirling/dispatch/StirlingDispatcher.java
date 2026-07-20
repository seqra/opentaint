package test.samples.stirling.dispatch;

import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;
import test.samples.StirlingTraceResolutionRegressionSample;
import test.samples.stirling.model.StirlingPdfRequest;

@RestController
public final class StirlingDispatcher {
    private StirlingTraceResolutionRegressionSample controller;

    @GetMapping()
    public ResponseEntity<byte[]> dispatch(StirlingPdfRequest request) {
        return controller.getPdfInfo(request);
    }
}
