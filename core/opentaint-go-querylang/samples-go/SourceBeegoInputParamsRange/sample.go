package util

func Sink(s string) { _ = s }

type beegoInput struct{}

func (i *beegoInput) Params() string { return "" }

type beegoContext struct{ Input *beegoInput }

type Controller struct{ Ctx *beegoContext }

func Positive_params_range_value(c *Controller) {
	data := c.Ctx.Input.Params()
	m := map[string]string{}
	m["k"] = data
	var param string
	for _, v := range m {
		param = v
	}
	Sink(param)
}

func Positive_params_range_key(c *Controller) {
	data := c.Ctx.Input.Params()
	m := map[string]string{}
	m[data] = "value"
	var param string
	for name := range m {
		param = name
	}
	Sink(param)
}

func Negative_const(c *Controller) {
	_ = c
	m := map[string]string{"k": "safe"}
	var param string
	for name := range m {
		param = name
	}
	Sink(param)
}
