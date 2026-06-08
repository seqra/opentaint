package util

import (
	"encoding/xml"
	"os"
	"strings"
)

// Note is the deserialization target.
type Note struct {
	Title string `xml:"title"`
}

// Positive_args_direct: CLI arg parsed as XML directly.
func Positive_args_direct() {
	a := os.Args[1]
	var out Note
	_ = xml.Unmarshal([]byte(a), &out)
}

// Positive_args_trimmed: trim does not sanitize.
func Positive_args_trimmed() {
	a := os.Args[2]
	t := strings.TrimSpace(a)
	var out Note
	_ = xml.Unmarshal([]byte(t), &out)
}

// Negative_args_logged: arg read but not used as sink input.
func Negative_args_logged() {
	_ = os.Args[1]
	var out Note
	_ = xml.Unmarshal([]byte(`<Note><title>safe</title></Note>`), &out)
}
