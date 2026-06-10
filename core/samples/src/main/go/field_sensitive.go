package test
import "test/util"


// ── Field sensitivity (struct fields) tests ──────────────────────────

// SFPair is a struct with tainted and clean fields
type SFPair struct {
	tainted string
	clean   string
}

// SFNested is a struct with a nested struct field
type SFNested struct {
	inner SFPair
	other string
}

// ── Direct field read/write ──────────────────────────────────────────

func structField001T() {
	data := util.Source()
	p := SFPair{tainted: data, clean: "safe"}
	util.Sink(p.tainted)
}

func structField002F() {
	data := util.Source()
	p := SFPair{tainted: data, clean: "safe"}
	util.Sink(p.clean)
}

func structFieldWrite001T() {
	data := util.Source()
	var p SFPair
	p.tainted = data
	util.Sink(p.tainted)
}

func structFieldWrite002F() {
	data := util.Source()
	var p SFPair
	p.tainted = data
	util.Sink(p.clean)
}

// ── Field sensitivity through function calls ─────────────────────────

func getPairTainted(p SFPair) string { return p.tainted }
func getPairClean(p SFPair) string   { return p.clean }

func structFieldInterproc001T() {
	data := util.Source()
	p := SFPair{tainted: data, clean: "safe"}
	result := getPairTainted(p)
	util.Sink(result)
}

func structFieldInterproc002F() {
	data := util.Source()
	p := SFPair{tainted: data, clean: "safe"}
	result := getPairClean(p)
	util.Sink(result)
}

// ── Nested struct field access ───────────────────────────────────────

func structNested001T() {
	data := util.Source()
	inner := SFPair{tainted: data, clean: "safe"}
	n := SFNested{inner: inner, other: "safe"}
	util.Sink(n.inner.tainted)
}

func structNested002F() {
	data := util.Source()
	inner := SFPair{tainted: data, clean: "safe"}
	n := SFNested{inner: inner, other: "safe"}
	util.Sink(n.other)
}
