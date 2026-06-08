package util

import (
	"net/http"
	"os"
	"text/template"
)

var w http.ResponseWriter

// Page is the model passed to a text/template renderer.
type Page struct {
	Title string
	Body  string
}

// Positive_struct_data: tainted env value embedded in struct data passed to Execute.
func Positive_struct_data() {
	t := template.Must(template.New("p").Parse("<h1>{{.Title}}</h1><p>{{.Body}}</p>"))
	body := os.Getenv("BODY")
	data := Page{Title: "Welcome", Body: body}
	_ = t.Execute(w, data)
}

// Negative_struct_const: struct fields are all constant.
func Negative_struct_const() {
	t := template.Must(template.New("p").Parse("<h1>{{.Title}}</h1><p>{{.Body}}</p>"))
	_ = os.Getenv("BODY")
	data := Page{Title: "Welcome", Body: "static"}
	_ = t.Execute(w, data)
}
