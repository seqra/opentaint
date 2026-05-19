package test
import "test/util"


// ── String operation tests ───────────────────────────────────────────

// ── String indexing ──────────────────────────────────────────────────

func stringIndex001T() {
	data := util.Source()
	b := data[0]
	result := string(b)
	util.Sink(result)
}

func stringIndex002F() {
	_ = util.Source()
	data := "safe"
	b := data[0]
	result := string(b)
	util.Sink(result)
}

// ── String slicing ───────────────────────────────────────────────────

func stringSlice001T() {
	data := util.Source()
	result := data[1:3]
	util.Sink(result)
}

func stringSlice002F() {
	_ = util.Source()
	data := "safe string"
	result := data[1:3]
	util.Sink(result)
}

// ── String through multiple variables ────────────────────────────────

func stringMultiVar001T() {
	a := util.Source()
	b := a
	c := b
	util.Sink(c)
}

func stringMultiVar002F() {
	a := util.Source()
	_ = a
	b := "safe"
	c := b
	util.Sink(c)
}

// ── String concat in loop ────────────────────────────────────────────

func stringConcatLoop001T() {
	data := util.Source()
	result := ""
	for i := 0; i < 3; i++ {
		result = result + data
	}
	util.Sink(result)
}

func stringConcatLoop002F() {
	_ = util.Source()
	result := ""
	for i := 0; i < 3; i++ {
		result = result + "safe"
	}
	util.Sink(result)
}
