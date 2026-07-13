package util

import (
	"database/sql"
	"net/http"
	"text/template"

	beegoctx "samples/TypedPatterns/context"
	"samples/TypedPatterns/web"
)

func Source() string { return "tainted" }
func Sink(s string)  { _ = s }

// Positive_typed_request_source: typed *http.Request receiver source
// (r.FormValue) flows to an untyped sink — isolates the typed SOURCE pattern.
func Positive_typed_request_source(r *http.Request) {
	s := r.FormValue("q")
	Sink(s)
}

func Positive_typed_beego_controller_source(c *web.Controller) {
	s := c.GetString("q")
	Sink(s)
}

func Positive_typed_beego_input_source(i *beegoctx.BeegoInput) {
	s := i.Param(":id")
	Sink(s)
}

// Positive_typed_sqldb_sink: untyped source flows to a typed *sql.DB.Query
// sink — isolates the typed SQL SINK pattern.
func Positive_typed_sqldb_sink(db *sql.DB) {
	q := Source()
	_, _ = db.Query(q)
}

// Positive_typed_httpclient_sink: untyped source flows to a typed
// *http.Client.Get sink — isolates the typed SSRF SINK pattern.
func Positive_typed_httpclient_sink(c *http.Client) {
	u := Source()
	_, _ = c.Get(u)
}

// Positive_typed_template_sink: untyped source flows to a typed
// *template.Template.Parse sink — isolates the typed SSTI SINK pattern.
func Positive_typed_template_sink(t *template.Template) {
	src := Source()
	_, _ = t.Parse(src)
}

// Negative_constant_sqldb: a constant query into the typed sink, no taint —
// must stay clean (focus is on the query argument).
func Negative_constant_sqldb(db *sql.DB) {
	_, _ = db.Query("SELECT 1")
}
