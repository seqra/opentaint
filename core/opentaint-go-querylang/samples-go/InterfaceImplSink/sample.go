package util

import "net/http"

func Source() string { return "tainted" }

type concreteRW struct{}

func (concreteRW) Header() http.Header         { return nil }
func (concreteRW) Write(p []byte) (int, error) { return len(p), nil }
func (concreteRW) WriteHeader(int)             {}

type notAWriter struct{}

func (notAWriter) Write(p []byte) (int, error) { return len(p), nil }

func Positive_concrete_impl_of_interface() {
	var w concreteRW
	_, _ = w.Write([]byte(Source()))
}

func Negative_not_responsewriter() {
	var b notAWriter
	_, _ = b.Write([]byte(Source()))
}
