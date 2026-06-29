package ecb

type blockMode struct{}

func NewECBEncrypter(args ...interface{}) *blockMode {
	return &blockMode{}
}

func NewECBDecrypter(args ...interface{}) *blockMode {
	return &blockMode{}
}
