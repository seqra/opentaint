package test
import "test/util"


// ── Basic intraprocedural flow tests ────────────────────────────────

func stringDirect() {
	util.Sink(util.Source())
}

func killByOverwrite001F() {
	data := util.Source()
	data = "safe"
	util.Sink(data)
}

func killByReassign001F() {
	data := util.Source()
	other := data
	other = "safe"
	util.Sink(other)
}

func noKill001T() {
	data := util.Source()
	other := data
	data = "safe"
	util.Sink(other)
}
