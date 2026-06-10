package test
import "test/util"


// ── Channel direction and usage pattern tests ────────────────────────

// ── Directional channels ─────────────────────────────────────────────

func chanDirection001T() {
	ch := make(chan string, 1)
	data := util.Source()
	ch <- data
	result := <-ch
	util.Sink(result)
}

func chanDirection002F() {
	ch := make(chan string, 1)
	_ = util.Source()
	ch <- "safe"
	result := <-ch
	util.Sink(result)
}

// ── Multiple sends on a channel ──────────────────────────────────────

func chanMultiSend001T() {
	ch := make(chan string, 3)
	ch <- "clean1"
	ch <- util.Source()
	ch <- "clean2"
	_ = <-ch
	result := <-ch
	util.Sink(result)
}

func chanMultiSend002F() {
	_ = util.Source()
	ch := make(chan string, 3)
	ch <- "clean1"
	ch <- "clean2"
	ch <- "clean3"
	_ = <-ch
	result := <-ch
	util.Sink(result)
}

// ── Function returning value from channel ────────────────────────────

func recvFromChan(ch chan string) string {
	return <-ch
}

func chanFunc001T() {
	ch := make(chan string, 1)
	data := util.Source()
	ch <- data
	result := recvFromChan(ch)
	util.Sink(result)
}

func chanFunc002F() {
	ch := make(chan string, 1)
	_ = util.Source()
	ch <- "safe"
	result := recvFromChan(ch)
	util.Sink(result)
}

// ── Channel passed to function that sends ────────────────────────────

func chanSendHelper(ch chan string, val string) {
	ch <- val
}

func chanPassThrough001T() {
	ch := make(chan string, 1)
	data := util.Source()
	chanSendHelper(ch, data)
	result := <-ch
	util.Sink(result)
}

func chanPassThrough002F() {
	ch := make(chan string, 1)
	_ = util.Source()
	chanSendHelper(ch, "safe")
	result := <-ch
	util.Sink(result)
}

// ── Channel receive in loop ──────────────────────────────────────────

func chanLoop001T() {
	ch := make(chan string, 3)
	ch <- util.Source()
	ch <- "a"
	ch <- "b"
	for i := 0; i < 3; i++ {
		val := <-ch
		if i == 0 {
			util.Sink(val)
		}
	}
}

func chanLoop002F() {
	_ = util.Source()
	ch := make(chan string, 3)
	ch <- "safe1"
	ch <- "safe2"
	ch <- "safe3"
	for i := 0; i < 3; i++ {
		val := <-ch
		if i == 0 {
			util.Sink(val)
		}
	}
}
