package util

import (
	"net/http"
	"os"
)

var client = &http.Client{}

func Positive_client_get() {
	u := os.Getenv("URL")
	_, _ = client.Get(u)
}

func Positive_http_get() {
	u := os.Getenv("URL")
	_, _ = http.Get(u)
}

func Negative_const_url() {
	_, _ = client.Get("https://safe.example.com")
}
