package util

import (
	"encoding/xml"
	"os"
)

// Rec is the deserialization target.
type Rec struct {
	V string `xml:"v"`
}

// splitBytes is a stub that returns multiple byte chunks; engine cannot
// propagate taint across slice elements, so we deliberately do NOT rely on
// element-level propagation in the positive case below.
func splitBytes(b []byte) [][]byte { return [][]byte{b} }

// Positive_loop: tainted env bytes are unmarshalled inside a loop body.
// The tainted variable itself is reused inside the loop (no slice-element prop).
func Positive_loop() {
	v := os.Getenv("XML_CHUNKS")
	src := []byte(v)
	chunks := splitBytes(src)
	for range chunks {
		var out Rec
		_ = xml.Unmarshal(src, &out)
	}
}

// Negative_loop_const: loop runs but a constant is decoded.
func Negative_loop_const() {
	_ = os.Getenv("XML_CHUNKS")
	for i := 0; i < 3; i++ {
		_ = i
		var out Rec
		_ = xml.Unmarshal([]byte(`<Rec><v>safe</v></Rec>`), &out)
	}
}
