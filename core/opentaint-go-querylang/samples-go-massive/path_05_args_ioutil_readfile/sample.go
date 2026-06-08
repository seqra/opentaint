package util

import (
	"io/ioutil"
	"os"
)

// Positive_args: os.Args[1] used directly as a file path.
func Positive_args() {
	p := os.Args[1]
	b, _ := ioutil.ReadFile(p)
	_ = b
}

// Positive_args_prefixed: os.Args[2] concatenated with a base dir.
func Positive_args_prefixed() {
	name := os.Args[2]
	b, _ := ioutil.ReadFile("/etc/app/" + name)
	_ = b
}

// Negative_const: args read but constant path used.
func Negative_const() {
	_ = os.Args[1]
	b, _ := ioutil.ReadFile("/etc/app/config.yaml")
	_ = b
}
