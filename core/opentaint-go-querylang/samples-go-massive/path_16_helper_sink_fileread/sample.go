package util

import (
	"net/http"
)

var r *http.Request

// Sink_FileRead represents a real 3rd-party file-read API (e.g. afero.Fs.ReadFile,
// embed.FS.ReadFile, or vfs.ReadFile) that loads bytes from the given path.
func Sink_FileRead(path string) ([]byte, error) { _ = path; return nil, nil }

// Positive_helper_sink: tainted form value flows directly into the file-read helper.
func Positive_helper_sink() {
	name := r.FormValue("doc")
	b, _ := Sink_FileRead("/srv/docs/" + name)
	_ = b
}

// Negative_const: form read but helper called with a constant.
func Negative_const() {
	_ = r.FormValue("doc")
	b, _ := Sink_FileRead("/srv/docs/static.txt")
	_ = b
}
