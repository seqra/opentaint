package util

import (
	"html/template"
	"os"
)

func Sink(s string) { _ = s }

func Positive_unescaped() {
	v := os.Getenv("X")
	Sink(v)
}

func Negative_escaped() {
	v := os.Getenv("X")
	Sink(template.HTMLEscapeString(v))
}
