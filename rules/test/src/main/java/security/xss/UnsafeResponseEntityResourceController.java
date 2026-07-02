package security.xss;

import java.nio.charset.StandardCharsets;

import org.springframework.core.io.ByteArrayResource;
import org.springframework.core.io.Resource;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

@RestController
public class UnsafeResponseEntityResourceController {

    @GetMapping("/unsafe-responseentity-resource")
    public ResponseEntity<Resource> unsafeResponseEntityResource(@RequestParam(required = false, defaultValue = "") String name) {
        return ResponseEntity.ok(new ByteArrayResource(("<h1>hi " + name + "</h1>").getBytes(StandardCharsets.UTF_8)));
    }
}
