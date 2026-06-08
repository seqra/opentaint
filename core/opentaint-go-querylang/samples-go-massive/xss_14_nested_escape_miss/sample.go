package util

import (
	"net/http"
	"os"
	"text/template"
)

var w http.ResponseWriter

// Positive_nested_escape_miss: the inner ("nested") env value was escaped,
// but the OUTER env value is concatenated into the response unescaped — sanitizer didn't cover the outer path.
func Positive_nested_escape_miss() {
	inner := os.Getenv("INNER")
	outer := os.Getenv("OUTER")
	safeInner := template.HTMLEscapeString(inner)
	body := "<div data-inner=\"" + safeInner + "\">" + outer + "</div>"
	w.Write([]byte(body))
}

// Negative_full_escape: both values escaped before reaching the sink.
func Negative_full_escape() {
	inner := os.Getenv("INNER")
	outer := os.Getenv("OUTER")
	safeInner := template.HTMLEscapeString(inner)
	safeOuter := template.HTMLEscapeString(outer)
	body := "<div data-inner=\"" + safeInner + "\">" + safeOuter + "</div>"
	w.Write([]byte(body))
}
