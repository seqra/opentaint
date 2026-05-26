package util

import (
	"encoding/json"
	"os"
)

// Late is the deserialization target.
type Late struct {
	X string `json:"x"`
}

// Positive_defer: deferred json.Unmarshal consumes tainted env value.
func Positive_defer() {
	v := os.Getenv("LATER")
	var out Late
	defer json.Unmarshal([]byte(v), &out)
}

// Negative_defer_const: defer fires but uses a constant payload.
func Negative_defer_const() {
	_ = os.Getenv("LATER")
	var out Late
	defer json.Unmarshal([]byte(`{"x":"safe"}`), &out)
}
