package allpatterns

import (
	"bytes"
	"html/template"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

type sqlClauseBuilder interface {
	where(string) string
}

type prefixClauseBuilder struct{}

func (prefixClauseBuilder) where(value string) string {
	return "name = '" + value + "'"
}

type queryHolder struct {
	where string
}

func buildSQLWhere(value string) string {
	return "name = '" + value + "'"
}

func PositiveSQLHelperReturnFlow() {
	r := requestForSources()
	_, _ = db.Query("select * from users where " + buildSQLWhere(r.Header.Get("X-Test")))
}

func PositiveSQLStructFieldFlow() {
	r := requestForSources()
	holder := queryHolder{where: r.URL.Query().Get("q")}
	_, _ = db.Query("select * from users where name = '" + holder.where + "'")
}

func PositiveSQLInterfaceDispatchFlow() {
	r := requestForSources()
	var builder sqlClauseBuilder = prefixClauseBuilder{}
	_, _ = db.Query("select * from users where " + builder.where(r.FormValue("q")))
}

func NegativeSQLParameterizedArgument() {
	_, _ = db.Query("select * from users where name = ?", envSource())
}

type commandJob struct {
	name string
}

type commandBuilder interface {
	build(string) string
}

type shellCommandBuilder struct{}

func (shellCommandBuilder) build(value string) string {
	return value
}

func commandName(value string) string {
	return value
}

func PositiveCmdHelperReturnFlow() {
	r := requestForSources()
	_ = exec.Command(commandName(r.URL.Query().Get("cmd"))).Run()
}

func PositiveCmdStructFieldFlow() {
	r := requestForSources()
	job := commandJob{name: r.Header.Get("X-Test")}
	_, _ = exec.LookPath(job.name)
}

func PositiveCmdInterfaceDispatchFlow() {
	r := requestForSources()
	var builder commandBuilder = shellCommandBuilder{}
	_ = exec.Command(builder.build(r.FormValue("cmd"))).Start()
}

type requestedFile struct {
	name string
}

type pathResolver interface {
	resolve(string) string
}

type joinResolver struct{}

func (joinResolver) resolve(value string) string {
	return filepath.Join("static", value)
}

func resolvePath(value string) string {
	return filepath.Join("static", value)
}

func PositivePathHelperReturnFlow() {
	r := requestForSources()
	_, _ = os.Open(resolvePath(r.URL.Query().Get("file")))
}

func PositivePathStructFieldFlow() {
	r := requestForSources()
	file := requestedFile{name: r.Header.Get("X-Test")}
	_, _ = os.ReadFile(file.name)
}

func PositivePathInterfaceDispatchFlow() {
	r := requestForSources()
	var resolver pathResolver = joinResolver{}
	_, _ = os.Stat(resolver.resolve(r.FormValue("file")))
}

func ssrfTarget(value string) string {
	return "https://" + value
}

func PositiveSSRFHelperReturnFlow() {
	r := requestForSources()
	_, _ = http.Get(ssrfTarget(r.URL.Query().Get("host")))
}

func PositiveSSRFChannelFlow() {
	r := requestForSources()
	ch := make(chan string, 1)
	ch <- r.Header.Get("X-Test")
	target := <-ch
	_, _ = client.Get("https://" + target)
}

func xssBody(value string) string {
	return "<p>" + value + "</p>"
}

func PositiveXSSHelperReturnFlow() {
	r := requestForSources()
	_, _ = responseWriterWithString{}.WriteString(xssBody(r.URL.Query().Get("q")))
}

func PositiveXSSChannelFlow() {
	r := requestForSources()
	ch := make(chan string, 1)
	ch <- r.FormValue("q")
	value := <-ch
	_, _ = responseWriterWithString{}.Write([]byte(value))
}

func PositiveSSTIBuilderChainFlow() {
	r := requestForSources()
	t := template.New("x").Funcs(template.FuncMap{"trim": strings.TrimSpace})
	_, _ = t.Parse(r.FormValue("template"))
}

func NegativeSSTIConstantTemplateTaintedData() {
	t := template.Must(template.New("x").Parse("hello {{.}}"))
	_ = t.Execute(&bytes.Buffer{}, envSource())
}

func PositiveTrustCookiePathFlow() {
	r := requestForSources()
	http.SetCookie(responseWriterWithString{}, &http.Cookie{Name: "session", Path: r.URL.Path})
}
