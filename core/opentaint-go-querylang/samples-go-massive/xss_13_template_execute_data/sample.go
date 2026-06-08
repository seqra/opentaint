package util

import (
	"html/template"
	"net/http"
)

var r *http.Request
var w http.ResponseWriter

// Positive_template_execute: tainted form value passed as Execute data.
func Positive_template_execute() {
	t := template.Must(template.New("p").Parse("<p>{{.}}</p>"))
	v := r.FormValue("body")
	_ = t.Execute(w, v)
}

// Negative_template_const: Execute called with a constant data value.
func Negative_template_const() {
	t := template.Must(template.New("p").Parse("<p>{{.}}</p>"))
	_ = r.FormValue("body")
	_ = t.Execute(w, "static body")
}
