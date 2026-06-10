package web

import (
	"mime/multipart"

	beegocontext "github.com/beego/beego/v2/server/web/context"
)

type Controller struct {
	Ctx *Context
}

type Context struct {
	Input *beegocontext.BeegoInput
}

func (c *Controller) GetString(key string, def ...string) string    { return "" }
func (c *Controller) GetStrings(key string, def ...string) []string { return nil }
func (c *Controller) GetInt(key string, def ...int) (int, error)    { return 0, nil }
func (c *Controller) GetInt8(key string) (int8, error)              { return 0, nil }
func (c *Controller) GetInt16(key string) (int16, error)            { return 0, nil }
func (c *Controller) GetInt32(key string) (int32, error)            { return 0, nil }
func (c *Controller) GetInt64(key string) (int64, error)            { return 0, nil }
func (c *Controller) GetUint8(key string) (uint8, error)            { return 0, nil }
func (c *Controller) GetUint16(key string) (uint16, error)          { return 0, nil }
func (c *Controller) GetUint32(key string) (uint32, error)          { return 0, nil }
func (c *Controller) GetUint64(key string) (uint64, error)          { return 0, nil }
func (c *Controller) GetFloat(key string) (float64, error)          { return 0, nil }
func (c *Controller) GetBool(key string) (bool, error)              { return false, nil }
func (c *Controller) GetFile(key string) (multipart.File, *multipart.FileHeader, error) {
	return nil, nil, nil
}
func (c *Controller) GetFiles(key string) ([]*multipart.FileHeader, error) { return nil, nil }
func (c *Controller) GetSession(key string) interface{}                    { return nil }
func (c *Controller) Input() map[string]string                             { return nil }
func (c *Controller) ParseForm(ptr interface{}) error                      { return nil }
func (c *Controller) SetSession(key string, value interface{}) error       { return nil }
