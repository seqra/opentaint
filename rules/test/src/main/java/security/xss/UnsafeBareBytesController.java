package security.xss;

import java.nio.charset.StandardCharsets;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

@RestController
public class UnsafeBareBytesController {

    @GetMapping("/unsafe-bare-bytes")
    public byte[] unsafeBareBytes(@RequestParam(required = false, defaultValue = "") String name) {
        return ("<h1>hi " + name + "</h1>").getBytes(StandardCharsets.UTF_8);
    }
}
