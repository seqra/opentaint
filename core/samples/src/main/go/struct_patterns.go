package test
import "test/util"


// ── Struct field access pattern tests ────────────────────────────────

type SPData struct {
	first  string
	second string
	third  string
}

// ── Struct literal with tainted field ────────────────────────────────

func structLiteral001T() {
	data := util.Source()
	s := SPData{first: data, second: "clean", third: "clean"}
	util.Sink(s.first)
}

func structLiteral002F() {
	data := util.Source()
	s := SPData{first: data, second: "clean", third: "clean"}
	util.Sink(s.second)
}

// ── Multi-field struct, selective access ──────────────────────────────

func structMultiField001T() {
	data := util.Source()
	s := SPData{first: data, second: "b", third: "c"}
	util.Sink(s.first)
}

func structMultiField002F() {
	data := util.Source()
	s := SPData{first: data, second: "b", third: "c"}
	util.Sink(s.second)
}

// ── Function returning struct ────────────────────────────────────────

func makeSPData(val string) SPData {
	return SPData{first: val, second: "safe", third: "safe"}
}

func structFuncReturn001T() {
	data := util.Source()
	s := makeSPData(data)
	util.Sink(s.first)
}

func structFuncReturn002F() {
	data := util.Source()
	s := makeSPData(data)
	util.Sink(s.second)
}

// ── Pointer to struct, dereference and read ──────────────────────────

func structPtrDeref001T() {
	data := util.Source()
	s := &SPData{first: data, second: "clean", third: "clean"}
	util.Sink(s.first)
}

func structPtrDeref002F() {
	data := util.Source()
	s := &SPData{first: data, second: "clean", third: "clean"}
	util.Sink(s.second)
}

// ── Struct field reassignment ────────────────────────────────────────

func structReassign001T() {
	data := util.Source()
	s := SPData{first: "clean", second: "clean", third: "clean"}
	s.first = data
	util.Sink(s.first)
}

func structReassign002F() {
	data := util.Source()
	s := SPData{first: "clean", second: "clean", third: "clean"}
	s.first = data
	util.Sink(s.second)
}
