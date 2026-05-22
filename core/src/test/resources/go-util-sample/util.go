package util

func Source() string { return "tainted" }

func Sink(s string) { _ = s }

func Run() {
	Sink(Source())
}
