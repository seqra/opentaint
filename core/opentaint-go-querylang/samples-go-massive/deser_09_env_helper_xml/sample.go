package util

import (
	"encoding/xml"
	"os"
)

// Msg is the deserialization target.
type Msg struct {
	Text string `xml:"text"`
}

// buildPayload wraps a string in an XML envelope.
func buildPayload(inner string) string {
	return "<Msg><text>" + inner + "</text></Msg>"
}

// Positive_helper_chain: env -> buildPayload -> xml.Unmarshal.
func Positive_helper_chain() {
	v := os.Getenv("RAW")
	p := buildPayload(v)
	var out Msg
	_ = xml.Unmarshal([]byte(p), &out)
}

// Negative_helper_const: helper called with constant; env unused.
func Negative_helper_const() {
	_ = os.Getenv("RAW")
	p := buildPayload("clean")
	var out Msg
	_ = xml.Unmarshal([]byte(p), &out)
}
