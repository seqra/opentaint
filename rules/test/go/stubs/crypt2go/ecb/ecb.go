package ecb

import "crypto/cipher"

type blockMode struct{}

func NewECBEncrypter(b cipher.Block) cipher.BlockMode {
	return &blockMode{}
}

func NewECBDecrypter(b cipher.Block) cipher.BlockMode {
	return &blockMode{}
}

func (x *blockMode) BlockSize() int              { return 0 }
func (x *blockMode) CryptBlocks(dst, src []byte) {}
