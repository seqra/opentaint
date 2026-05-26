package util

import (
	"bufio"
	"encoding/json"
	"os"
)

// Req models a JSON request body containing a user-supplied filename.
type Req struct {
	Filename string `json:"filename"`
}

// Positive_json: raw JSON body read from stdin, decoded, field used as file path.
func Positive_json() {
	raw, _ := bufio.NewReader(os.Stdin).ReadString('\n')
	var req Req
	_ = json.Unmarshal([]byte(raw), &req)
	f, _ := os.Open("/srv/data/" + req.Filename)
	_ = f
}

// Negative_const: JSON read but a constant path opened.
func Negative_const() {
	_, _ = bufio.NewReader(os.Stdin).ReadString('\n')
	f, _ := os.Open("/srv/data/index.bin")
	_ = f
}
