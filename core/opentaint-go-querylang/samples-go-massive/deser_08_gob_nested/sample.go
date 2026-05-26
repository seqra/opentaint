package util

import (
	"encoding/gob"
	"os"
	"strings"
)

// State is the deserialization target.
type State struct {
	Field string
}

// Positive_gob_nested: tainted env wrapped in strings.NewReader, decoded via gob.
// Sink is the outer .Decode; tainted flows through the inner strings.NewReader.
func Positive_gob_nested() {
	s := os.Getenv("GOB_DATA")
	var out State
	_ = gob.NewDecoder(strings.NewReader(s)).Decode(&out)
}

// Negative_gob_const: env read but a constant reader is decoded.
func Negative_gob_const() {
	_ = os.Getenv("GOB_DATA")
	var out State
	_ = gob.NewDecoder(strings.NewReader("safe-const")).Decode(&out)
}
