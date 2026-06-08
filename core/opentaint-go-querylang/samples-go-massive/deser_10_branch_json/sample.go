package util

import (
	"encoding/json"
	"os"
)

// Opts is the deserialization target.
type Opts struct {
	A string `json:"a"`
}

// Positive_branch: tainted value is taken on the "if" branch then decoded.
func Positive_branch() {
	v := os.Getenv("FLAG")
	var s string
	if len(v) > 0 {
		s = v
	} else {
		s = `{"a":"default"}`
	}
	var out Opts
	_ = json.Unmarshal([]byte(s), &out)
}

// Negative_branch_const_only: constant branch chosen regardless of env.
func Negative_branch_const_only() {
	v := os.Getenv("FLAG")
	_ = v
	s := `{"a":"only-const"}`
	var out Opts
	_ = json.Unmarshal([]byte(s), &out)
}
