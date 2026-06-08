package util

import (
	"os"
)

// Positive_args_writefile: password from os.Args[2] (--password) written to log file.
func Positive_args_writefile() {
	pw := os.Args[2]
	_ = os.WriteFile("/tmp/audit.log", []byte("pw="+pw), 0644)
}

// Negative_args_writefile_const: args read but constant body written.
func Negative_args_writefile_const() {
	_ = os.Args[2]
	_ = os.WriteFile("/tmp/audit.log", []byte("pw=***"), 0644)
}
