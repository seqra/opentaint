package test
import "test/util"


// ── Advanced control flow tests ──────────────────────────────────────

// ── Switch/case ──────────────────────────────────────────────────────

func switchCase001T() {
	data := util.Source()
	var result string
	switch data {
	case "a":
		result = data
	case "b":
		result = data
	default:
		result = data
	}
	util.Sink(result)
}

func switchCase002F() {
	data := util.Source()
	var result string
	switch data {
	case "a":
		result = "safe"
	case "b":
		result = "safe"
	default:
		result = "safe"
	}
	util.Sink(result)
	util.Consume(data)
}

func switchFallthrough001T() {
	data := util.Source()
	var result string
	switch 1 {
	case 1:
		result = data
		fallthrough
	case 2:
		// result keeps value from case 1
	}
	util.Sink(result)
}

// ── For-range ────────────────────────────────────────────────────────

func forRange001T() {
	data := util.Source()
	s := []string{data, "a", "b"}
	var result string
	for _, v := range s {
		result = v
	}
	util.Sink(result)
}

func forRange002F() {
	data := util.Source()
	s := []string{"a", "b", "c"}
	var result string
	for _, v := range s {
		result = v
	}
	util.Sink(result)
	util.Consume(data)
}

func forRangeMap001T() {
	data := util.Source()
	m := map[string]string{"k": data}
	var result string
	for _, v := range m {
		result = v
	}
	util.Sink(result)
}

func forRangeMap002F() {
	data := util.Source()
	m := map[string]string{"k": "safe"}
	var result string
	for _, v := range m {
		result = v
	}
	util.Sink(result)
	util.Consume(data)
}

// ── Break and continue ───────────────────────────────────────────────

func breakInLoop001T() {
	data := util.Source()
	var result string
	for i := 0; i < 10; i++ {
		if i == 5 {
			result = data
			break
		}
	}
	util.Sink(result)
}

func breakInLoop002F() {
	data := util.Source()
	var result string
	for i := 0; i < 10; i++ {
		result = "safe"
		if i == 5 {
			break
		}
	}
	util.Sink(result)
	util.Consume(data)
}

func continueInLoop001T() {
	data := util.Source()
	var result string
	for i := 0; i < 3; i++ {
		if i == 0 {
			continue
		}
		result = data
	}
	util.Sink(result)
}

// ── Labeled break ────────────────────────────────────────────────────

func labeledBreak001T() {
	data := util.Source()
	var result string
outer:
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			if j == 1 {
				result = data
				break outer
			}
		}
	}
	util.Sink(result)
}

// ── Nested loops ─────────────────────────────────────────────────────

func nestedLoop001T() {
	data := util.Source()
	var result string
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			result = data
		}
	}
	util.Sink(result)
}

func nestedLoop002F() {
	data := util.Source()
	var result string
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			result = "safe"
		}
	}
	util.Sink(result)
	util.Consume(data)
}

// ── Select statement ─────────────────────────────────────────────────

func selectStmt001T() {
	data := util.Source()
	ch := make(chan string, 1)
	ch <- data
	var result string
	select {
	case result = <-ch:
	}
	util.Sink(result)
}
