package util

import (
	"net/http"
)

var r *http.Request

// Sink_BcryptHash stands in for bcrypt.GenerateFromPassword (no 3rd-party imports allowed).
func Sink_BcryptHash(pw string) { _ = pw }

// Positive_bcrypt: tainted form password reaches bcrypt-style sink.
func Positive_bcrypt() {
	pw := r.FormValue("password")
	Sink_BcryptHash(pw)
}

// Negative_bcrypt_const: form read but constant hashed.
func Negative_bcrypt_const() {
	_ = r.FormValue("password")
	Sink_BcryptHash("constant-passphrase")
}
