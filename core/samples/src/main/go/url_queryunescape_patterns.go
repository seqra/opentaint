package test

import (
	"net/http"
	"net/url"

	"test/util"
)

func queryUnescapeMultiRet001T() {
	data := util.Source()
	clean, _ := url.QueryUnescape(data)
	util.Sink(clean)
}

func queryUnescapeMultiRet002F() {
	_, _ = url.QueryUnescape("safe")
	util.Sink("safe")
}

func queryUnescapeReassign001T() {
	data := util.Source()
	data, _ = url.QueryUnescape(data)
	util.Sink(data)
}

func fprintfStub(w string, format string, a ...interface{}) {
	_ = w
	_ = format
	_ = a
}

func queryUnescapeFprintfSpread001T() {
	var param string
	referer := util.Source()
	if referer != "" {
		param = referer
	}
	param, _ = url.QueryUnescape(param)
	obj := []interface{}{"a", "b"}
	fprintfStub("w", param, obj...)
}

func queryUnescapeFprintfSpread002F() {
	param := "safe"
	param, _ = url.QueryUnescape(param)
	obj := []interface{}{"a", "b"}
	fprintfStub("w", param, obj...)
}

func sourceHeader() http.Header {
	return http.Header{}
}

func headerGetFprintf001T() {
	h := sourceHeader()
	var param string
	referer := h.Get("Referer")
	if referer != "" {
		param = referer
	}
	param, _ = url.QueryUnescape(param)
	obj := []interface{}{"a", "b"}
	fprintfStub("w", param, obj...)
}

func headerGetSink001T() {
	h := sourceHeader()
	referer := h.Get("Referer")
	util.Sink(referer)
}
