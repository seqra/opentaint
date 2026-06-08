package util

import (
	"crypto/aes"
	"crypto/cipher"
	"net/http"
)

var r *http.Request

// Positive_iv_arg: form value flows into IV arg (2nd) of CBC encrypter.
func Positive_iv_arg() {
	iv := r.FormValue("iv")
	block, _ := aes.NewCipher([]byte("0123456789abcdef"))
	_ = cipher.NewCBCEncrypter(block, []byte(iv))
}

// Negative_block_only: form value not used in IV; focus-metavariable means NOT a finding.
func Negative_block_only() {
	_ = r.FormValue("iv")
	block, _ := aes.NewCipher([]byte("0123456789abcdef"))
	_ = cipher.NewCBCEncrypter(block, []byte("0000000000000000"))
}
