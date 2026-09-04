package org.springframework.http;

public class HttpEntity<T> {
    public T Body;

    public HttpEntity() { }

    public HttpEntity(T body) {
        this.Body = body;
    }
}
