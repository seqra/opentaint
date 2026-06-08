package test
import "test/util"


// ── Control flow tests ──────────────────────────────────────────────

func conditionalIf001T() {
	data := util.Source()
	var result string
	if len(data) > 0 {
		result = data
	} else {
		result = "safe"
	}
	util.Sink(result)
}

func conditionalIf002F() {
	data := util.Source()
	var result string
	if len(data) > 0 {
		result = "safe"
	} else {
		result = "safe"
	}
	util.Sink(result)
	util.Consume(data)
}

func forBody001T() {
	data := util.Source()
	var result string
	for i := 0; i < 1; i++ {
		result = data
	}
	util.Sink(result)
}

func forBody002F() {
	data := util.Source()
	var result string
	for i := 0; i < 1; i++ {
		result = "safe"
	}
	util.Sink(result)
	util.Consume(data)
}
