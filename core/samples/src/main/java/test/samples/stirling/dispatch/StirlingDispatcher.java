package test.samples.stirling.dispatch;

import org.springframework.http.ResponseEntity;
import test.samples.StirlingTraceResolutionRegressionSample;

/** Starts outside the controller so trace resolution must cross the controller and response helper. */
public final class StirlingDispatcher {
    public ResponseEntity<byte[]> dispatch() {
        StirlingTraceResolutionRegressionSample controller =
                new StirlingTraceResolutionRegressionSample();
        controller.cleanResponse();
        return controller.getPdfInfo(new StirlingTraceResolutionRegressionSample.Request());
    }
}
