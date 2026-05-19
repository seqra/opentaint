package test
import "test/util"


// ── Variable shadowing tests ─────────────────────────────────────────

func shadow001T() {
	data := util.Source()
	{
		// inner block: data still visible
		util.Sink(data)
	}
}

func shadow002F() {
	data := util.Source()
	func() {
		data := "safe" // shadowed in inner func
		util.Sink(data)
	}()
	util.Consume(data)
}

func shadow003T() {
	data := "safe"
	func() {
		data := util.Source() // shadowed with tainted in inner func
		util.Sink(data)
	}()
	util.Consume(data)
}

func shadow004F() {
	data := util.Source()
	if true {
		data = "safe" // overwritten
	}
	util.Sink(data)
}

// ── Shadowing in for loop ────────────────────────────────────────────

func shadowLoop001T() {
	data := util.Source()
	for i := 0; i < 1; i++ {
		result := data // new variable
		util.Sink(result)
	}
}

func shadowLoop002F() {
	data := util.Source()
	for i := 0; i < 1; i++ {
		local := "safe"
		util.Sink(local)
	}
	util.Consume(data)
}

// ── Shadowing with function params ───────────────────────────────────

func shadowParam001T() {
	data := util.Source()
	shadowHelper(data)
}

func shadowHelper(data string) {
	util.Sink(data)
}

func shadowParam002F() {
	data := util.Source()
	_ = data
	shadowHelper("safe")
}
