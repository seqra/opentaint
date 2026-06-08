package test
import "test/util"


// ── Multiple return value tests ──────────────────────────────────────

func twoReturns(a string, b string) (string, string) {
	return a, b
}

func threeReturns(a string, b string, c string) (string, string, string) {
	return a, b, c
}

// Named return values
func namedReturns(input string) (result string, err string) {
	result = input
	err = ""
	return
}

func namedReturnsClean(input string) (result string, err string) {
	result = "safe"
	err = ""
	return
}

// ── Basic multi-return ───────────────────────────────────────────────

func multiReturn001T() {
	data := util.Source()
	first, _ := twoReturns(data, "clean")
	util.Sink(first)
}

func multiReturn002F() {
	data := util.Source()
	_, second := twoReturns(data, "clean")
	util.Sink(second)
}

func multiReturn003T() {
	data := util.Source()
	_, second := twoReturns("clean", data)
	util.Sink(second)
}

func multiReturn004F() {
	data := util.Source()
	first, _ := twoReturns("clean", data)
	util.Sink(first)
}

// ── Three return values ──────────────────────────────────────────────

func threeReturn001T() {
	data := util.Source()
	first, _, _ := threeReturns(data, "b", "c")
	util.Sink(first)
}

func threeReturn002F() {
	data := util.Source()
	_, second, _ := threeReturns(data, "b", "c")
	util.Sink(second)
}

func threeReturn003T() {
	data := util.Source()
	_, _, third := threeReturns("a", "b", data)
	util.Sink(third)
}

// ── Named return values ──────────────────────────────────────────────

func namedReturn001T() {
	data := util.Source()
	result, _ := namedReturns(data)
	util.Sink(result)
}

func namedReturn002F() {
	data := util.Source()
	result, _ := namedReturnsClean(data)
	util.Sink(result)
}

// ── Discard with blank identifier ────────────────────────────────────

func blankIdentifier001T() {
	data := util.Source()
	result, _ := twoReturns(data, "x")
	util.Sink(result)
}

func blankIdentifier002F() {
	data := util.Source()
	_, result := twoReturns(data, "x")
	util.Sink(result)
}
