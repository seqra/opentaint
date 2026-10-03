package util

type Input struct {
	ID    string
	Clean string
}

func Sink(string) {}

type Runner interface {
	Run()
}

type ConcreteRunner struct {
	Path string
}

func (r *ConcreteRunner) Run() {
	Sink(r.Path)
}

func NewConcrete(in *Input) *ConcreteRunner {
	return &ConcreteRunner{Path: in.ID}
}

func NewInterface(in *Input) Runner {
	return &ConcreteRunner{Path: in.ID}
}

func NewClean(in *Input) *ConcreteRunner {
	return &ConcreteRunner{Path: in.Clean}
}

type ConcreteFactory func(*Input) *ConcreteRunner
type InterfaceResultFactory func(*Input) Runner

type Client struct {
	ConcreteFactory        ConcreteFactory
	InterfaceResultFactory InterfaceResultFactory
}

func NewClient() *Client {
	return &Client{
		ConcreteFactory:        NewConcrete,
		InterfaceResultFactory: NewInterface,
	}
}

var defaultClient = NewClient()

type FactoryObject interface {
	Create(*Input) *ConcreteRunner
}

type ConcreteFactoryObject struct{}

func (*ConcreteFactoryObject) Create(in *Input) *ConcreteRunner {
	return &ConcreteRunner{Path: in.ID}
}

type InterfaceClient struct {
	Factory FactoryObject
}

func Positive_direct_field_source(in *Input) {
	Sink(in.ID)
}

func Positive_direct_named_factory(in *Input) {
	runner := NewConcrete(in)
	runner.Run()
}

func Positive_locally_initialized_func_field(in *Input) {
	client := &Client{ConcreteFactory: NewConcrete}
	runner := client.ConcreteFactory(in)
	runner.Run()
}

func Positive_constructor_then_method(in *Input) {
	client := NewClient()
	client.opaqueConcreteFuncField(in)
}

func (client *InterfaceClient) helperOpaqueInterfaceMethod(in *Input) {
	runner := client.Factory.Create(in)
	runner.Run()
}

func (client *Client) opaqueConcreteFuncField(in *Input) {
	runner := client.ConcreteFactory(in)
	runner.Run()
}

func (client *Client) helperOpaqueInterfaceResultFuncField(in *Input) {
	runner := client.InterfaceResultFactory(in)
	runner.Run()
}

func Positive_package_initialized_global(in *Input) {
	defaultClient.opaqueConcreteFuncField(in)
}

func Negative_clean_field(in *Input) {
	runner := NewClean(in)
	runner.Run()
}
