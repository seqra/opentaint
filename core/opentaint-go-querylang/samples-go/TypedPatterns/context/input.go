package context

type BeegoInput struct{}

func (i *BeegoInput) Param(key string) string {
	return ""
}
