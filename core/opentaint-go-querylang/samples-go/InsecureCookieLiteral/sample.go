package util

import "net/http"

func Positive_insecure_cookie_literal() *http.Cookie {
	return &http.Cookie{Name: "session", Value: "x", Secure: false}
}

func Negative_secure_cookie() *http.Cookie {
	return &http.Cookie{Name: "session", Value: "x", Secure: true}
}
