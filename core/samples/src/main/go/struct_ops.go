package test
import "test/util"


// ── Additional struct operation tests ────────────────────────────────

// ── Struct copy semantics ────────────────────────────────────────────

type SOData struct {
	value string
	extra string
}

func structCopy001T() {
	data := util.Source()
	original := SOData{value: data, extra: "x"}
	copied := original
	util.Sink(copied.value)
}

func structCopy002F() {
	data := util.Source()
	original := SOData{value: data, extra: "x"}
	copied := original
	util.Sink(copied.extra)
}

func structCopy003T() {
	data := util.Source()
	original := SOData{value: data, extra: "x"}
	copied := original
	original.value = "safe" // mutating original doesn't affect copy
	util.Sink(copied.value)
}

// ── Struct as function argument (value semantics) ────────────────────

func readSOValue(d SOData) string { return d.value }
func readSOExtra(d SOData) string { return d.extra }

func structArg001T() {
	data := util.Source()
	d := SOData{value: data, extra: "x"}
	result := readSOValue(d)
	util.Sink(result)
}

func structArg002F() {
	data := util.Source()
	d := SOData{value: data, extra: "x"}
	result := readSOExtra(d)
	util.Sink(result)
}

// ── Struct returned from function ────────────────────────────────────

func makeSOData(val string) SOData {
	return SOData{value: val, extra: "x"}
}

func structReturn001T() {
	data := util.Source()
	d := makeSOData(data)
	util.Sink(d.value)
}

func structReturn002F() {
	data := util.Source()
	d := makeSOData(data)
	util.Sink(d.extra)
}

// ── Nested struct modification ───────────────────────────────────────

type SOOuter struct {
	inner SOData
	label string
}

func nestedStructMod001T() {
	data := util.Source()
	o := SOOuter{
		inner: SOData{value: data, extra: "x"},
		label: "y",
	}
	util.Sink(o.inner.value)
}

func nestedStructMod002F() {
	data := util.Source()
	o := SOOuter{
		inner: SOData{value: data, extra: "x"},
		label: "y",
	}
	util.Sink(o.label)
}

func nestedStructMod003F() {
	data := util.Source()
	o := SOOuter{
		inner: SOData{value: data, extra: "x"},
		label: "y",
	}
	util.Sink(o.inner.extra)
}

// ── Struct pointer field modification ────────────────────────────────

func structPtrField001T() {
	data := util.Source()
	d := &SOData{}
	d.value = data
	util.Sink(d.value)
}

func structPtrField002F() {
	data := util.Source()
	d := &SOData{}
	d.value = data
	util.Sink(d.extra)
}

// ── Struct with method modifying field ───────────────────────────────

type SOWithMethod struct {
	data string
}

func (s *SOWithMethod) Set(val string) { s.data = val }
func (s SOWithMethod) Get() string     { return s.data }

func structMethod001T() {
	data := util.Source()
	s := &SOWithMethod{}
	s.Set(data)
	result := s.Get()
	util.Sink(result)
}

func structMethod002F() {
	_ = util.Source()
	s := &SOWithMethod{}
	s.Set("safe")
	result := s.Get()
	util.Sink(result)
}
