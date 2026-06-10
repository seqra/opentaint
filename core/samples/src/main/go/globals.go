package test
import "test/util"


// ── Global variable tests ────────────────────────────────────────────

func globalWrite001T() {
	util.GlobalTainted = util.Source()
	util.Sink(util.GlobalTainted)
}

func globalWrite002F() {
	_ = util.Source()
	util.GlobalClean = "still safe"
	util.Sink(util.GlobalClean)
}

func globalWriteRead001T() {
	util.GlobalTainted = util.Source()
	result := util.GlobalTainted
	util.Sink(result)
}

func globalWriteRead002F() {
	_ = util.Source()
	util.GlobalClean = "safe"
	result := util.GlobalClean
	util.Sink(result)
}

// ── Global through function ──────────────────────────────────────────

func setGlobal(val string) {
	util.GlobalTainted = val
}

func getGlobal() string {
	return util.GlobalTainted
}

func globalFunc001T() {
	data := util.Source()
	setGlobal(data)
	result := getGlobal()
	util.Sink(result)
}

func globalFunc002F() {
	_ = util.Source()
	setGlobal("safe")
	result := getGlobal()
	util.Sink(result)
}

// ── Global struct ────────────────────────────────────────────────────

type GlobalHolder struct {
	data string
}

var globalHolder GlobalHolder

func globalStruct001T() {
	globalHolder.data = util.Source()
	util.Sink(globalHolder.data)
}

func globalStruct002F() {
	_ = util.Source()
	globalHolder.data = "safe"
	util.Sink(globalHolder.data)
}
