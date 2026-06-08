package util

import (
	"encoding/json"
	"net/http"
	"os"
)

var r *http.Request

// Combo is the deserialization target.
type Combo struct {
	A string `json:"a"`
	B string `json:"b"`
}

// Positive_merge: env and URL query concatenated into one JSON body.
func Positive_merge() {
	a := os.Getenv("A_PART")
	b := r.URL.Query().Get("b")
	body := `{"a":"` + a + `","b":"` + b + `"}`
	var out Combo
	_ = json.Unmarshal([]byte(body), &out)
}

// Negative_merge_unused: both sources read but unused; constant decoded.
func Negative_merge_unused() {
	_ = os.Getenv("A_PART")
	_ = r.URL.Query().Get("b")
	var out Combo
	_ = json.Unmarshal([]byte(`{"a":"safe","b":"safe"}`), &out)
}
