package util

import (
	"os"
	"text/template"
)

func Positive_parse_tainted_source() {
	src := os.Getenv("TMPL")
	_, _ = template.New("x").Parse(src)
}

func Negative_parse_constant() {
	_, _ = template.New("x").Parse("Hello {{.}}")
}
