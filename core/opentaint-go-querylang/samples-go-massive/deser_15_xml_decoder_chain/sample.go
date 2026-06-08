package util

import (
	"encoding/xml"
	"net/http"
	"strings"
)

var r *http.Request

// Wrap is the deserialization target.
type Wrap struct {
	Body string `xml:"body"`
}

// Positive_decoder_chain: tainted header -> strings.NewReader -> xml.NewDecoder -> Decode.
func Positive_decoder_chain() {
	h := r.Header.Get("X-Doc")
	var out Wrap
	_ = xml.NewDecoder(strings.NewReader(h)).Decode(&out)
}

// Negative_decoder_chain_const: header read but constant decoded.
func Negative_decoder_chain_const() {
	_ = r.Header.Get("X-Doc")
	var out Wrap
	_ = xml.NewDecoder(strings.NewReader(`<Wrap><body>safe</body></Wrap>`)).Decode(&out)
}
