package util

type Request struct{}

func (*Request) AdmittedRequest() {}

type Admitted interface {
	AdmittedRequest()
}

type Server struct{}

type Context struct{}

func (*Server) Authenticate(*Context, Admitted)         {}
func (*Server) AuthenticateConcrete(*Context, *Request) {}
func (*Server) RaftApply(int, any)                      {}

type Endpoint struct{}

func Positive_free_function(args *Request) {
	server := &Server{}
	server.Authenticate(nil, args)
	server.RaftApply(0, args)
}

func (*Endpoint) Positive_method_concrete_source(args *Request) {
	server := &Server{}
	server.AuthenticateConcrete(nil, args)
	server.RaftApply(0, args)
}

func (*Endpoint) Positive_method_reuses_source_interface(args *Request) {
	server := &Server{}
	admitted := Admitted(args)
	server.Authenticate(nil, admitted)
	server.RaftApply(0, admitted)
}

func (*Endpoint) Positive_method_parameter_reboxed(args *Request) {
	server := &Server{}
	server.Authenticate(nil, args)
	server.RaftApply(0, args)
}

func (*Endpoint) Negative_no_admission(args *Request) {
	server := &Server{}
	server.RaftApply(0, args)
}
