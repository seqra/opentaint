package security.xss;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

@RestController
public class UnsafeHtmlRestController {

    @GetMapping(value = "/unsafe-html", produces = "text/html")
    public String unsafeHtml(@RequestParam(required = false, defaultValue = "") String name) {
        return "<h1>Hello, " + name + "!</h1>";
    }
}
