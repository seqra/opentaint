package util

import (
	"net/http"
	"os"
)

var r *http.Request

// Positive_merge: dir from env, filename from header — both tainted, both flow to os.Open.
func Positive_merge() {
	dir := os.Getenv("DIR")
	name := r.Header.Get("X-File")
	f, _ := os.Open(dir + "/" + name)
	_ = f
}

// Positive_env_only: only env reaches the sink; header read but discarded.
func Positive_env_only() {
	dir := os.Getenv("DIR")
	_ = r.Header.Get("X-File")
	f, _ := os.Open(dir + "/data.bin")
	_ = f
}

// Negative_const_merge: both sources read but a constant path is opened.
func Negative_const_merge() {
	_ = os.Getenv("DIR")
	_ = r.Header.Get("X-File")
	f, _ := os.Open("/var/data/static.bin")
	_ = f
}
