package test.samples;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;

/**
 * Two independent taint flows that share one sink method.
 *
 * echo() is a purely local flow that both the field-insensitive shallow pass and the
 * field-sensitive full pass discover.
 *
 * upload()/resync() is the Stirling-PDF shape: one request handler stores request data into a
 * Spring singleton (a ClassStatic access path) and a different handler reads it back through a
 * getter chain into the sink.
 */
@RestController
public final class ShallowRuleSelectionSample {
    @Autowired
    private LicenseService licenseService;

    @GetMapping
    public void upload(UploadRequest request) {
        licenseService.store(request);
    }

    @GetMapping
    public void resync() {
        sink(licenseService.read());
    }

    @GetMapping
    public void echo(UploadRequest request) {
        sink(request.getName());
    }

    @GetMapping
    public void echoSecond(UploadRequest first, UploadRequest second) {
        sink(second.getName());
    }

    public static void sink(String path) {
        System.out.println(path);
    }

    public static class UploadRequest {
        private String name;

        public String getName() {
            return this.name;
        }
    }

    public static class LicenseService {
        private final Premium premium = new Premium();

        public void store(UploadRequest request) {
            this.premium.setKey(request.getName());
        }

        public String read() {
            return this.premium.getKey();
        }
    }

    public static class Premium {
        private String key;

        public String getKey() {
            return this.key;
        }

        public void setKey(String key) {
            this.key = key;
        }
    }
}
