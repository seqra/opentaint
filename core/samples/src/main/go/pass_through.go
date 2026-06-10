package test
import "test/util"


// ── Pass-through rule tests ──────────────────────────────────────────

func passThrough001T() {
	data := util.Source()
	result := util.Passthrough(data)
	util.Sink(result)
}

func passThrough002F() {
	data := util.Source()
	result := util.Sanitize(data)
	util.Sink(result)
}

func passThrough003T() {
	data := util.Source()
	result := util.Transform(data, "other")
	util.Sink(result)
}

func passThrough004F() {
	result := util.Transform("clean", util.Source())
	util.Sink(result)
}
