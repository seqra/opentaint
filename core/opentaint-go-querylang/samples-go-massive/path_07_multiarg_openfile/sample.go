package util

import (
	"net/http"
	"os"
	"strconv"
)

var r *http.Request

// Positive_path_arg: tainted form value lands in the path arg ($P) — the focus-metavariable.
func Positive_path_arg() {
	name := r.FormValue("file")
	f, _ := os.OpenFile("/var/data/"+name, os.O_RDONLY, 0)
	_ = f
}

// Negative_flag_arg: tainted form value lands in the flag arg ($FLAG), not $P. Should NOT report.
func Negative_flag_arg() {
	raw := r.FormValue("flag")
	flag, _ := strconv.Atoi(raw)
	f, _ := os.OpenFile("/var/data/static.txt", flag, 0)
	_ = f
}
