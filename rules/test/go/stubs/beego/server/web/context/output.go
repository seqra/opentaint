package context

type BeegoOutput struct{}

func (output *BeegoOutput) Body(content []byte) error { return nil }

func (output *BeegoOutput) JSON(data interface{}, hasIndent bool, coding bool) error { return nil }

type Response struct{}

func (r *Response) Write(p []byte) (int, error) { return len(p), nil }

type Context struct {
	Input          *BeegoInput
	Output         *BeegoOutput
	ResponseWriter *Response
}

func (ctx *Context) WriteString(content string) {}
