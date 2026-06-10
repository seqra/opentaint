package util

import (
	"log"
	"os"
)

var l *log.Logger

// Positive_logoutput_msg: PRIVATE_KEY embedded into log.Output message arg.
func Positive_logoutput_msg() {
	k := os.Getenv("PRIVATE_KEY")
	_ = l.Output(2, "key="+k)
}

// Negative_logoutput_const: env read but message arg is constant.
func Negative_logoutput_const() {
	_ = os.Getenv("PRIVATE_KEY")
	_ = l.Output(2, "key=<redacted>")
}
