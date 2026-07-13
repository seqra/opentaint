package util

import (
	"fmt"
	"net/http"
)

func Source() string { return "tainted" }

func Positive_typed_arg(w http.ResponseWriter) {
	_, _ = fmt.Fprint(w, Source())
}

func Negative_const(w http.ResponseWriter) {
	_, _ = fmt.Fprint(w, "safe")
}
