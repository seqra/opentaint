package util

import (
	"encoding/xml"
	"os"
)

// Item is the deserialization target.
type Item struct {
	Name string `xml:"name"`
}

// Positive_basic: env var bytes directly into xml.Unmarshal (XXE-style data injection).
func Positive_basic() {
	v := os.Getenv("XML_PAYLOAD")
	var out Item
	_ = xml.Unmarshal([]byte(v), &out)
}

// Negative_const: env read but constant XML used.
func Negative_const() {
	_ = os.Getenv("XML_PAYLOAD")
	var out Item
	_ = xml.Unmarshal([]byte(`<Item><name>safe</name></Item>`), &out)
}
