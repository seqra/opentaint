package util

import (
	"fmt"
	"log"
	"net/http"
)

var r *http.Request

// Positive_postform_logprint: PostFormValue formatted via Sprintf then log.Print (newline injection).
func Positive_postform_logprint() {
	v := r.PostFormValue("comment")
	msg := fmt.Sprintf("comment=%s", v)
	log.Print(msg)
}

// Negative_postform_const: PostFormValue read but constant logged.
func Negative_postform_const() {
	_ = r.PostFormValue("comment")
	log.Print("comment=<n/a>")
}
