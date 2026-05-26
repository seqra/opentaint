package util

import (
	"os"
)

// Positive_lookupenv: use only the string return of os.LookupEnv as a file path.
func Positive_lookupenv() {
	p, _ := os.LookupEnv("CFG_PATH")
	f, _ := os.Open(p)
	_ = f
}

// Positive_lookupenv_prefixed: string return concatenated into a path then opened.
func Positive_lookupenv_prefixed() {
	name, _ := os.LookupEnv("CFG_PATH")
	f, _ := os.Open("/etc/app/" + name)
	_ = f
}

// Negative_const: LookupEnv called but a constant path is opened.
func Negative_const() {
	_, _ = os.LookupEnv("CFG_PATH")
	f, _ := os.Open("/etc/app/config.yaml")
	_ = f
}
