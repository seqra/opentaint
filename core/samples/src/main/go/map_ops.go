package test
import "test/util"


// ── Additional map operation tests ───────────────────────────────────

// ── Map with struct values ───────────────────────────────────────────

type MapItem struct {
	data  string
	label string
}

func mapStruct001T() {
	data := util.Source()
	m := map[string]MapItem{
		"key": {data: data, label: "x"},
	}
	util.Sink(m["key"].data)
}

func mapStruct002F() {
	data := util.Source()
	m := map[string]MapItem{
		"key": {data: data, label: "x"},
	}
	util.Sink(m["key"].label)
}

// ── Map iteration ────────────────────────────────────────────────────

func mapIter001T() {
	data := util.Source()
	m := map[string]string{"k1": data, "k2": "safe"}
	var result string
	for _, v := range m {
		result = v
	}
	util.Sink(result)
}

func mapIter002F() {
	data := util.Source()
	m := map[string]string{"k1": "safe", "k2": "safe"}
	var result string
	for _, v := range m {
		result = v
	}
	util.Sink(result)
	util.Consume(data)
}

// ── Map key taint ────────────────────────────────────────────────────

func mapKeyTaint001T() {
	data := util.Source()
	m := map[string]string{data: "value"}
	for k := range m {
		util.Sink(k)
	}
}

// ── Map delete doesn't affect taint ──────────────────────────────────

func mapDelete001T() {
	data := util.Source()
	m := map[string]string{"k1": data, "k2": "safe"}
	delete(m, "k1") // delete doesn't kill taint in analysis
	util.Sink(m["k1"])
}

// ── Map comma-ok lookup ──────────────────────────────────────────────

func mapCommaOk001T() {
	data := util.Source()
	m := map[string]string{"k": data}
	v, ok := m["k"]
	if ok {
		util.Sink(v)
	}
}

func mapCommaOk002F() {
	_ = util.Source()
	m := map[string]string{"k": "safe"}
	v, ok := m["k"]
	if ok {
		util.Sink(v)
	}
}
