package org.springframework.http;

public class ResponseEntity<T> extends HttpEntity<T> {

    public ResponseEntity() { }

    public ResponseEntity(T body) { super(body); }

    public ResponseEntity(T body, HttpHeaders headers, HttpStatus status) {
        super(body);
    }
}
