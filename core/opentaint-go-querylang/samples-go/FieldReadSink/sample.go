package util

type Holder struct{ Field string }

func Source() string { return "tainted" }

func Positive_field_read_sink() {
	var h Holder
	h.Field = Source()
	_ = h.Field
}

func Negative_const() {
	var h Holder
	h.Field = "safe"
	_ = h.Field
}
