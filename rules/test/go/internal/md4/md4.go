package md4

type Digest struct{}

func New(args ...interface{}) *Digest {
	return &Digest{}
}
