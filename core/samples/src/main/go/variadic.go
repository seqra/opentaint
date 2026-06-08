package test
import "test/util"


// ── Variadic function tests ──────────────────────────────────────────

func varJoin(parts ...string) string {
	result := ""
	for _, p := range parts {
		result = result + p
	}
	return result
}

func varFirst(parts ...string) string {
	if len(parts) > 0 {
		return parts[0]
	}
	return ""
}

func varLast(parts ...string) string {
	if len(parts) > 0 {
		return parts[len(parts)-1]
	}
	return ""
}

// ── Tests ────────────────────────────────────────────────────────────

func variadic001T() {
	data := util.Source()
	result := varJoin(data, "b", "c")
	util.Sink(result)
}

func variadic002F() {
	_ = util.Source()
	result := varJoin("a", "b", "c")
	util.Sink(result)
}

func variadic003T() {
	data := util.Source()
	result := varFirst(data, "b")
	util.Sink(result)
}

func variadic004F() {
	data := util.Source()
	result := varFirst("safe", data)
	// varFirst returns first arg which is "safe"
	util.Sink(result)
}

func variadic005T() {
	data := util.Source()
	result := varLast("a", data)
	util.Sink(result)
}

func variadic006F() {
	data := util.Source()
	result := varLast(data, "safe")
	// varLast returns last arg which is "safe"
	util.Sink(result)
}

// ── Spread slice into variadic ───────────────────────────────────────

func variadicSpread001T() {
	data := util.Source()
	args := []string{data, "b"}
	result := varFirst(args...)
	util.Sink(result)
}

func variadicSpread002T() {
	data := util.Source()
	args := []string{"a", data}
	result := varJoin(args...)
	util.Sink(result)
}
