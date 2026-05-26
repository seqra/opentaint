package util

import (
	"net/http"
	"os"
)

var w http.ResponseWriter

// taintedList returns a []string seeded from a tainted env value (avoids strings.Split limitation).
func taintedList() []string {
	v := os.Getenv("ITEMS")
	return []string{v, v + "-2", v + "-3"}
}

// Positive_loop_range: each tainted element written inside the loop body.
func Positive_loop_range() {
	items := taintedList()
	for _, it := range items {
		w.Write([]byte("<li>" + it + "</li>"))
	}
}

// Negative_loop_const: same loop shape but writing only the loop index, no tainted element.
func Negative_loop_const() {
	items := taintedList()
	for range items {
		w.Write([]byte("<li>safe</li>"))
	}
}
