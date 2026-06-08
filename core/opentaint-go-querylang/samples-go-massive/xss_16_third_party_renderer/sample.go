package util

import (
	"net/http"
)

var r *http.Request

// Sink_HtmlOutput represents a 3rd-party templating/renderer call site that emits HTML to the client.
func Sink_HtmlOutput(html string) { _ = html }

// Positive_3rdparty: tainted form value handed to a custom HTML renderer.
func Positive_3rdparty() {
	v := r.FormValue("post")
	Sink_HtmlOutput("<article>" + v + "</article>")
}

// Negative_3rdparty_const: renderer called with a static template.
func Negative_3rdparty_const() {
	_ = r.FormValue("post")
	Sink_HtmlOutput("<article>nothing posted yet</article>")
}
