package util

type Cookie struct{ Value string }

func Source() *Cookie { return &Cookie{Value: "tainted"} }

func SourceSlice() []*Cookie { return []*Cookie{{Value: "tainted"}} }

func Sink(s string) { _ = s }

func Positive_cookie_value_field_read() {
	c := Source()
	Sink(c.Value)
}

func Positive_cookie_value_range() {
	for _, ck := range SourceSlice() {
		Sink(ck.Value)
	}
}

func Negative_untainted_field() {
	c := &Cookie{Value: "safe"}
	Sink(c.Value)
}

func Negative_const() {
	Sink("safe")
}
