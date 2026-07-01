module test

go 1.22

require (
	github.com/andreburgaud/crypt2go v1.0.0
	github.com/beego/beego/v2 v2.0.0
	golang.org/x/crypto v0.21.0
)

replace github.com/beego/beego/v2 => ./stubs/beego

replace golang.org/x/crypto => ./stubs/x-crypto

replace github.com/andreburgaud/crypt2go => ./stubs/crypt2go
