package util

import (
	"net/http"
	"os"
)

var w http.ResponseWriter

// Positive_if_branch: env value selected on the true branch is written.
func Positive_if_branch() {
	var body string
	if os.Getenv("MODE") != "" {
		body = os.Getenv("MODE")
	} else {
		body = "default"
	}
	w.Write([]byte("<p>" + body + "</p>"))
}

// Negative_if_const: env consulted but only constants written on both branches.
func Negative_if_const() {
	var body string
	if os.Getenv("MODE") != "" {
		body = "on"
	} else {
		body = "off"
	}
	w.Write([]byte("<p>" + body + "</p>"))
}
