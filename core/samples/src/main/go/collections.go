package test
import "test/util"


// ── Collection sensitivity tests (slices, maps, arrays) ─────────────
// Key model: key-insensitive, but element-level vs container are distinct.

// ── Slice tests ──────────────────────────────────────────────────────

func sliceElem001T() {
	data := util.Source()
	s := make([]string, 3)
	s[0] = data
	util.Sink(s[0])
}

func sliceElem002T() {
	data := util.Source()
	s := make([]string, 3)
	s[0] = data
	util.Sink(s[1]) // key-insensitive: any element access on tainted container
}

func sliceLiteral001T() {
	data := util.Source()
	s := []string{data, "clean"}
	util.Sink(s[0])
}

func sliceCopy001T() {
	data := util.Source()
	s := make([]string, 3)
	s[0] = data
	s2 := s
	util.Sink(s2[0])
}

func slicePassToFunc001T() {
	data := util.Source()
	s := make([]string, 3)
	s[0] = data
	readSlice(s)
}

func readSlice(s []string) {
	util.Sink(s[0])
}

func sliceReturnElem001T() {
	data := util.Source()
	s := make([]string, 3)
	s[0] = data
	result := getSliceElem(s)
	util.Sink(result)
}

func getSliceElem(s []string) string {
	return s[0]
}

func sliceOverwrite001F() {
	data := util.Source()
	s := make([]string, 3)
	s[0] = data
	s[0] = "safe"
	util.Sink(s[0])
}

// ── Map tests ────────────────────────────────────────────────────────

func mapElem001T() {
	data := util.Source()
	m := make(map[string]string)
	m["key1"] = data
	util.Sink(m["key1"])
}

func mapElem002T() {
	data := util.Source()
	m := make(map[string]string)
	m["key1"] = data
	util.Sink(m["key2"]) // key-insensitive
}

func mapLiteral001T() {
	data := util.Source()
	m := map[string]string{"k": data}
	util.Sink(m["k"])
}

func mapPassToFunc001T() {
	data := util.Source()
	m := make(map[string]string)
	m["k"] = data
	readMap(m)
}

func readMap(m map[string]string) {
	util.Sink(m["k"])
}

func mapReturnElem001T() {
	data := util.Source()
	m := make(map[string]string)
	m["k"] = data
	result := getMapElem(m)
	util.Sink(result)
}

func getMapElem(m map[string]string) string {
	return m["k"]
}

// ── Array tests ──────────────────────────────────────────────────────

func arrayElem001T() {
	data := util.Source()
	var a [3]string
	a[0] = data
	util.Sink(a[0])
}

func arrayElem002T() {
	data := util.Source()
	var a [3]string
	a[0] = data
	util.Sink(a[1]) // key-insensitive
}

func arrayPassToFunc001T() {
	data := util.Source()
	var a [3]string
	a[0] = data
	readArray(a)
}

func readArray(a [3]string) {
	util.Sink(a[0])
}

// ── Mixed: slice of structs ──────────────────────────────────────────

type CollItem struct {
	value string
	label string
}

func sliceOfStructs001T() {
	data := util.Source()
	items := []CollItem{{value: data, label: "x"}}
	util.Sink(items[0].value)
}

func sliceOfStructs002F() {
	data := util.Source()
	items := []CollItem{{value: data, label: "x"}}
	util.Sink(items[0].label)
}
