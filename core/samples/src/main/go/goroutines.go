package test
import "test/util"


// ── Goroutine and channel tests ──────────────────────────────────────

// ── Channel send/receive ─────────────────────────────────────────────

func channel001T() {
	data := util.Source()
	ch := make(chan string, 1)
	ch <- data
	result := <-ch
	util.Sink(result)
}

func channel002F() {
	_ = util.Source()
	ch := make(chan string, 1)
	ch <- "safe"
	result := <-ch
	util.Sink(result)
}

// ── Goroutine with channel ───────────────────────────────────────────

func goroutineChan001T() {
	data := util.Source()
	ch := make(chan string, 1)
	go func() {
		ch <- data
	}()
	result := <-ch
	util.Sink(result)
}

func goroutineChan002F() {
	_ = util.Source()
	ch := make(chan string, 1)
	go func() {
		ch <- "safe"
	}()
	result := <-ch
	util.Sink(result)
}

// ── Goroutine with shared variable (through closure) ─────────────────

func goroutineShared001T() {
	data := util.Source()
	done := make(chan bool, 1)
	var result string
	go func() {
		result = data
		done <- true
	}()
	<-done
	util.Sink(result)
}

// ── Buffered channel ─────────────────────────────────────────────────

func bufferedChan001T() {
	data := util.Source()
	ch := make(chan string, 10)
	ch <- data
	ch <- "extra"
	result := <-ch
	util.Sink(result)
}

func bufferedChan002F() {
	_ = util.Source()
	ch := make(chan string, 10)
	ch <- "safe"
	result := <-ch
	util.Sink(result)
}

// ── Channel passed to function ───────────────────────────────────────

func sendToChan(ch chan string, val string) {
	ch <- val
}

func chanArg001T() {
	data := util.Source()
	ch := make(chan string, 1)
	sendToChan(ch, data)
	result := <-ch
	util.Sink(result)
}

func chanArg002F() {
	_ = util.Source()
	ch := make(chan string, 1)
	sendToChan(ch, "safe")
	result := <-ch
	util.Sink(result)
}
