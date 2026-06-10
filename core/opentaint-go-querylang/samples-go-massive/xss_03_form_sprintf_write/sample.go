package util

import (
	"fmt"
	"net/http"
)

var r *http.Request
var w http.ResponseWriter

// Positive_form_sprintf: form value formatted into HTML and written.
func Positive_form_sprintf() {
	v := r.FormValue("comment")
	body := fmt.Sprintf("<div class=\"c\">%s</div>", v)
	w.Write([]byte(body))
}

// Negative_const_body: form read but constant HTML written.
func Negative_const_body() {
	_ = r.FormValue("comment")
	body := fmt.Sprintf("<div class=\"c\">%s</div>", "no comment")
	w.Write([]byte(body))
}
