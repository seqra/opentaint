package util

import (
	"encoding/json"
	"os"
	"strings"
)

// J is the deserialization target.
type J struct {
	Field string `json:"field"`
}

// Positive_decoder: tainted env -> strings.NewReader -> json.NewDecoder -> Decode.
func Positive_decoder() {
	v := os.Getenv("JSON_BLOB")
	var out J
	_ = json.NewDecoder(strings.NewReader(v)).Decode(&out)
}

// Negative_decoder_const: env read but constant fed to the reader.
func Negative_decoder_const() {
	_ = os.Getenv("JSON_BLOB")
	var out J
	_ = json.NewDecoder(strings.NewReader(`{"field":"safe"}`)).Decode(&out)
}
