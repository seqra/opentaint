package test.samples.stirling.common;

import org.springframework.http.HttpHeaders;
import org.springframework.http.HttpStatus;
import org.springframework.http.MediaType;
import org.springframework.http.ResponseEntity;

public final class StirlingWebResponseUtils {
    private StirlingWebResponseUtils() { }

    public static ResponseEntity<byte[]> bytesToWebResponse(
            byte[] bytes, String documentName, MediaType mediaType) {
        HttpHeaders headers = new HttpHeaders();
        headers.setContentType(mediaType);
        headers.setContentLength(bytes.length);
        headers.setContentDispositionFormData("attachment", documentName);
        return new ResponseEntity<>(bytes, headers, HttpStatus.OK);
    }
}
