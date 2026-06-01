package util

import (
	"fmt"
	"net/http"
	"net/url"
	"os"
)

func Positive_header_queryunescape(r *http.Request) {
	var param string
	referer := r.Header.Get("Referer")
	if referer != "" {
		param = referer
	}
	param, _ = url.QueryUnescape(param)
	obj := []interface{}{"a", "b"}
	fmt.Fprintf(os.Stdout, param, obj...)
}

func Positive_header_direct(r *http.Request) {
	param := r.Header.Get("Referer")
	fmt.Fprintf(os.Stdout, param)
}

type Ctx struct {
	Request *http.Request
}

type Controller struct {
	Ctx Ctx
}

func (c *Controller) Positive_beego_shape() {
	var param string
	referer := c.Ctx.Request.Header.Get("Referer")
	if referer != "" {
		param = referer
	}
	param, _ = url.QueryUnescape(param)
	obj := []interface{}{"a", "b"}
	fmt.Fprintf(os.Stdout, param, obj...)
}

func Negative_const() {
	fmt.Fprintf(os.Stdout, "safe")
}
