package context

import (
	"net/http"
	"net/url"
)

type BeegoInput struct {
	RequestBody []byte
}

func (i *BeegoInput) Param(key string) string    { return "" }
func (i *BeegoInput) Header(key string) string   { return "" }
func (i *BeegoInput) Params() map[string]string  { return nil }
func (i *BeegoInput) URI() string                { return "" }
func (i *BeegoInput) URL() *url.URL              { return nil }
func (i *BeegoInput) Bind(ptr interface{}) error { return nil }
func (i *BeegoInput) Cookie(key string) string   { return "" }

var _ = http.Header{}
