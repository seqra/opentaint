package test
import "test/util"


import "errors"

// ── Error handling pattern tests ─────────────────────────────────────

// ── Error return value ───────────────────────────────────────────────

func mayFail(input string) (string, error) {
	if input == "" {
		return "", errors.New("empty")
	}
	return input, nil
}

func mayFailClean(input string) (string, error) {
	return "safe", nil
}

func errorReturn001T() {
	data := util.Source()
	result, err := mayFail(data)
	if err == nil {
		util.Sink(result)
	}
}

func errorReturn002F() {
	data := util.Source()
	result, err := mayFailClean(data)
	if err == nil {
		util.Sink(result)
	}
}

func errorReturn003T() {
	data := util.Source()
	result, _ := mayFail(data)
	util.Sink(result)
}

// ── Error wrapping ───────────────────────────────────────────────────

func wrapResult(input string) (string, error) {
	r, err := mayFail(input)
	if err != nil {
		return "", err
	}
	return r, nil
}

func errorWrap001T() {
	data := util.Source()
	result, _ := wrapResult(data)
	util.Sink(result)
}

func errorWrap002F() {
	data := util.Source()
	_, _ = wrapResult(data) // discard result
	util.Sink("safe")
}

// ── Early return on error ────────────────────────────────────────────

func earlyReturn001T() {
	data := util.Source()
	result, err := mayFail(data)
	if err != nil {
		return
	}
	util.Sink(result)
}

func earlyReturn002F() {
	data := util.Source()
	_, err := mayFail(data)
	if err != nil {
		return
	}
	util.Sink("safe")
}
