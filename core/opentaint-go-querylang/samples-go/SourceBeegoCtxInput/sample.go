package util

func Sink(s string) { _ = s }

type beegoInput struct{}

func (i *beegoInput) Query(k string) string { return "" }

type beegoContext struct{ Input *beegoInput }

type Controller struct{ Ctx *beegoContext }

func Positive_ctx_input(c *Controller) {
	Sink(c.Ctx.Input.Query("X-Test"))
}

func Negative_const(c *Controller) {
	_ = c
	Sink("safe")
}
