package test
import "test/util"


// ── Multiple taint mark tests ────────────────────────────────────────

func taintMarkMatch001T() {
	data := util.SourceA()
	util.SinkA(data)
}

func taintMarkMismatch001F() {
	data := util.SourceA()
	util.SinkB(data)
}

func taintMarkMatch002T() {
	data := util.SourceB()
	util.SinkB(data)
}
