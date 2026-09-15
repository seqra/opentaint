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

func passThrough005T() {
	result := util.GenericIdentity[string](util.Source())
	util.Sink(result)
}

func passThrough006T() {
	data := util.NamedString(util.Source())
	util.Sink(string(data))
}

func passThrough007T() {
	data := util.NamedString(util.Source())
	result := util.GenericIdentity[util.NamedString](data)
	util.Sink(string(result))
}
