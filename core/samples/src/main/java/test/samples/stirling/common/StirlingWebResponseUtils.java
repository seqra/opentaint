package test.samples.stirling.common;

import java.io.IOException;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;

import org.springframework.http.HttpHeaders;
import org.springframework.http.HttpStatus;
import org.springframework.http.MediaType;
import org.springframework.http.ResponseEntity;

public final class StirlingWebResponseUtils {
    private StirlingWebResponseUtils() { }

    public static ResponseEntity<byte[]> bytesToWebResponse(
            byte[] bytes, String documentName, MediaType mediaType) throws IOException {
        HttpHeaders headers = new HttpHeaders();
        headers.setContentType(mediaType);
        headers.setContentLength(bytes.length);
        String encodedDocumentName =
                URLEncoder.encode(documentName, StandardCharsets.UTF_8).replace("+", "%20");
        headers.setContentDispositionFormData("attachment", encodedDocumentName);
        return new ResponseEntity<>(bytes, headers, HttpStatus.OK);
    }
}
