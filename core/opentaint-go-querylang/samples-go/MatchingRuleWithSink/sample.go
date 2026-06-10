package util

func Sink(s string) { _ = s }

func Source() string { return "tainted"}

func Positive_form_index() {
	var src = Source()
	Sink(src)
}

func Negative_const() {
	Sink("safe")
}
