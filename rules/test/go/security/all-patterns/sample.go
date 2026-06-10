package allpatterns

import (
	"context"
	"crypto/des"
	"crypto/md5"
	"crypto/rc4"
	"crypto/sha1"
	"database/sql"
	"encoding/json"
	"fmt"
	"html"
	"html/template"
	"io"
	"io/ioutil"
	"math/rand"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"strings"
	"syscall"
	"time"

	"github.com/beego/beego/v2/server/web"
	beegocontext "github.com/beego/beego/v2/server/web/context"

	md4 "test/internal/md4"
	cipher "test/internal/weakcipher"
)

var (
	db     *sql.DB
	client = &http.Client{}
	ctx    = context.Background()
)

type responseWriterWithString struct{}

func (responseWriterWithString) Header() http.Header               { return http.Header{} }
func (responseWriterWithString) Write(p []byte) (int, error)       { return len(p), nil }
func (responseWriterWithString) WriteHeader(statusCode int)        {}
func (responseWriterWithString) WriteString(s string) (int, error) { return len(s), nil }

type beegoOutput struct{}

func (beegoOutput) Body(body string)                           {}
func (beegoOutput) JSON(data interface{}, args ...interface{}) {}

type jsonController struct {
	Data interface{}
}

func (c *jsonController) ServeJSON() {}

func requestForSources() *http.Request {
	r := &http.Request{
		URL:        &url.URL{Path: "/path", RawPath: "/raw-path", RawQuery: "q=v"},
		Header:     http.Header{"X-Test": []string{"header"}},
		Trailer:    http.Header{"X-Test": []string{"trailer"}},
		Form:       url.Values{"q": []string{"form"}},
		PostForm:   url.Values{"q": []string{"post"}},
		Body:       io.NopCloser(strings.NewReader("body")),
		RemoteAddr: "127.0.0.1:1",
	}
	r.RequestURI = "/path?q=v"
	r.GetBody = func() (io.ReadCloser, error) {
		return io.NopCloser(strings.NewReader("body")), nil
	}
	return r
}

func sqlSink(value interface{}) {
	_, _ = db.Query(fmt.Sprint(value))
}

func sqlSinkMany(value ...interface{}) {
	_, _ = db.Query(fmt.Sprint(value...))
}

func envSource() string {
	return os.Getenv("TAINTED")
}

func cookieFrom(value string) *http.Cookie {
	return &http.Cookie{Name: "session", Value: value}
}

func PositiveSourceRequestFormValue()     { r := requestForSources(); sqlSink(r.FormValue("q")) }
func PositiveSourceRequestPostFormValue() { r := requestForSources(); sqlSink(r.PostFormValue("q")) }
func UnsupportedPositiveSourceRequestFormFile() {
	r := requestForSources()
	f, _, _ := r.FormFile("file")
	sqlSink(f)
}
func UnsupportedPositiveSourceRequestCookie() {
	r := requestForSources()
	c, _ := r.Cookie("q")
	sqlSink(c)
}
func PositiveSourceRequestCookies() { r := requestForSources(); sqlSink(r.Cookies()) }
func UnsupportedPositiveSourceRequestMultipartReader() {
	r := requestForSources()
	mr, _ := r.MultipartReader()
	sqlSink(mr)
}
func PositiveSourceRequestReferer()   { r := requestForSources(); sqlSink(r.Referer()) }
func PositiveSourceRequestUserAgent() { r := requestForSources(); sqlSink(r.UserAgent()) }
func PositiveSourceURLQuery()         { r := requestForSources(); sqlSink(r.URL.Query()) }
func PositiveSourceURLQueryGet()      { r := requestForSources(); sqlSink(r.URL.Query().Get("q")) }
func PositiveSourceURLPath()          { r := requestForSources(); sqlSink(r.URL.Path) }
func PositiveSourceURLRawQuery()      { r := requestForSources(); sqlSink(r.URL.RawQuery) }
func PositiveSourceURLRawPath()       { r := requestForSources(); sqlSink(r.URL.RawPath) }
func PositiveSourceHeaderGet()        { r := requestForSources(); sqlSink(r.Header.Get("X-Test")) }
func PositiveSourceHeaderMap()        { r := requestForSources(); sqlSink(r.Header["X-Test"]) }
func PositiveSourceHeaderMapIndex()   { r := requestForSources(); sqlSink(r.Header["X-Test"][0]) }
func PositiveSourceFormMap()          { r := requestForSources(); sqlSink(r.Form["q"]) }
func PositiveSourceFormMapIndex()     { r := requestForSources(); sqlSink(r.Form["q"][0]) }
func PositiveSourcePostFormMap()      { r := requestForSources(); sqlSink(r.PostForm["q"]) }
func PositiveSourcePostFormMapIndex() { r := requestForSources(); sqlSink(r.PostForm["q"][0]) }
func PositiveSourceURLQueryMap()      { r := requestForSources(); sqlSink(r.URL.Query()["q"]) }
func PositiveSourceURLQueryMapIndex() { r := requestForSources(); sqlSink(r.URL.Query()["q"][0]) }
func PositiveSourceHeaderValues()     { r := requestForSources(); sqlSink(r.Header.Values("X-Test")) }
func PositiveSourceFormGet()          { r := requestForSources(); sqlSink(r.Form.Get("q")) }
func PositiveSourcePostFormGet()      { r := requestForSources(); sqlSink(r.PostForm.Get("q")) }
func PositiveSourceBody()             { r := requestForSources(); sqlSink(r.Body) }
func PositiveSourceGetBody()          { r := requestForSources(); sqlSink(r.GetBody) }
func PositiveSourceForm()             { r := requestForSources(); sqlSink(r.Form) }
func PositiveSourcePostForm()         { r := requestForSources(); sqlSink(r.PostForm) }
func PositiveSourceMultipartForm()    { r := requestForSources(); sqlSink(r.MultipartForm) }
func PositiveSourceHeader()           { r := requestForSources(); sqlSink(r.Header) }
func PositiveSourceTrailer()          { r := requestForSources(); sqlSink(r.Trailer) }
func PositiveSourceURL()              { r := requestForSources(); sqlSink(r.URL) }
func PositiveSourceGetenv()           { sqlSink(os.Getenv("TAINTED")) }
func UnsupportedPositiveSourceLookupEnv() {
	v, _ := os.LookupEnv("TAINTED")
	sqlSink(v)
}
func PositiveSourceArgs()       { sqlSink(os.Args) }
func PositiveSourceRequestURI() { r := requestForSources(); sqlSink(r.RequestURI) }

func PositiveSourceBeegoGetString()         { c := &web.Controller{}; sqlSink(c.GetString("q")) }
func PositiveSourceBeegoGetStringDefault()  { c := &web.Controller{}; sqlSink(c.GetString("q", "d")) }
func PositiveSourceBeegoGetStrings()        { c := &web.Controller{}; sqlSink(c.GetStrings("q")) }
func PositiveSourceBeegoGetStringsDefault() { c := &web.Controller{}; sqlSink(c.GetStrings("q", "d")) }
func PositiveSourceBeegoGetStringsIndex()   { c := &web.Controller{}; sqlSink(c.GetStrings("q")[0]) }
func PositiveSourceBeegoGetStringsDefaultIndex() {
	c := &web.Controller{}
	sqlSink(c.GetStrings("q", "d")[0])
}
func UnsupportedPositiveSourceBeegoGetInt() {
	c := &web.Controller{}
	v, _ := c.GetInt("q")
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetIntDefault() {
	c := &web.Controller{}
	v, _ := c.GetInt("q", 1)
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetInt8() {
	c := &web.Controller{}
	v, _ := c.GetInt8("q")
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetInt16() {
	c := &web.Controller{}
	v, _ := c.GetInt16("q")
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetInt32() {
	c := &web.Controller{}
	v, _ := c.GetInt32("q")
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetInt64() {
	c := &web.Controller{}
	v, _ := c.GetInt64("q")
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetUint8() {
	c := &web.Controller{}
	v, _ := c.GetUint8("q")
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetUint16() {
	c := &web.Controller{}
	v, _ := c.GetUint16("q")
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetUint32() {
	c := &web.Controller{}
	v, _ := c.GetUint32("q")
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetUint64() {
	c := &web.Controller{}
	v, _ := c.GetUint64("q")
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetFloat() {
	c := &web.Controller{}
	v, _ := c.GetFloat("q")
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetBool() {
	c := &web.Controller{}
	v, _ := c.GetBool("q")
	sqlSink(v)
}
func UnsupportedPositiveSourceBeegoGetFile() {
	c := &web.Controller{}
	f, _, _ := c.GetFile("q")
	sqlSink(f)
}
func UnsupportedPositiveSourceBeegoGetFiles() {
	c := &web.Controller{}
	f, _ := c.GetFiles("q")
	sqlSink(f)
}
func PositiveSourceBeegoGetSession() { c := &web.Controller{}; sqlSink(c.GetSession("q")) }
func PositiveSourceBeegoInput()      { c := &web.Controller{}; sqlSink(c.Input()) }
func UnsupportedPositiveSourceBeegoParseForm() {
	c := &web.Controller{}
	var dst struct{ Q string }
	sqlSinkMany(c.ParseForm(&dst))
}

func PositiveSourceBeegoInputParam()       { i := &beegocontext.BeegoInput{}; sqlSink(i.Param("q")) }
func PositiveSourceBeegoInputParams()      { i := &beegocontext.BeegoInput{}; sqlSink(i.Params()) }
func PositiveSourceBeegoInputURI()         { i := &beegocontext.BeegoInput{}; sqlSink(i.URI()) }
func PositiveSourceBeegoInputURL()         { i := &beegocontext.BeegoInput{}; sqlSink(i.URL()) }
func PositiveSourceBeegoInputRequestBody() { i := &beegocontext.BeegoInput{}; sqlSink(i.RequestBody) }
func UnsupportedPositiveSourceBeegoInputBind() {
	i := &beegocontext.BeegoInput{}
	var dst struct{ Q string }
	sqlSinkMany(i.Bind(&dst))
}
func PositiveSourceHeaderMethod() {
	i := &beegocontext.BeegoInput{}
	sqlSink(i.Header("q"))
}
func PositiveTrustSourceBeegoInputHeader() {
	i := &beegocontext.BeegoInput{}
	http.SetCookie(responseWriterWithString{}, cookieFrom(i.Header("q")))
}

func PositiveSQLDBQuery()           { _, _ = db.Query("select " + envSource()) }
func PositiveSQLDBQueryContext()    { _, _ = db.QueryContext(ctx, "select "+envSource()) }
func PositiveSQLDBQueryRow()        { _ = db.QueryRow("select " + envSource()) }
func PositiveSQLDBQueryRowContext() { _ = db.QueryRowContext(ctx, "select "+envSource()) }
func PositiveSQLDBExec()            { _, _ = db.Exec("select " + envSource()) }
func PositiveSQLDBExecContext()     { _, _ = db.ExecContext(ctx, "select "+envSource()) }
func PositiveSQLDBPrepare()         { _, _ = db.Prepare("select " + envSource()) }
func PositiveSQLDBPrepareContext()  { _, _ = db.PrepareContext(ctx, "select "+envSource()) }

func PositiveCmdExecCommand()        { _ = exec.Command(envSource(), "arg") }
func PositiveCmdExecCommandContext() { _ = exec.CommandContext(ctx, envSource(), "arg") }
func PositiveCmdExecLookPath()       { _, _ = exec.LookPath(envSource()) }
func PositiveCmdOSStartProcess() {
	_, _ = os.StartProcess(envSource(), []string{envSource()}, &os.ProcAttr{})
}
func PositiveCmdSyscallExec() { _ = syscall.Exec(envSource(), []string{envSource()}, os.Environ()) }
func PositiveCmdSyscallForkExec() {
	_, _ = syscall.ForkExec(envSource(), []string{envSource()}, &syscall.ProcAttr{})
}
func PositiveCmdSyscallStartProcess() {
	_, _, _ = syscall.StartProcess(envSource(), []string{envSource()}, &syscall.ProcAttr{})
}
func PositiveCmdCombinedOutput() { _, _ = exec.Command(envSource()).CombinedOutput() }
func PositiveCmdRun()            { _ = exec.Command(envSource()).Run() }
func PositiveCmdOutput()         { _, _ = exec.Command(envSource()).Output() }
func PositiveCmdStart()          { _ = exec.Command(envSource()).Start() }

func PositivePathOSOpen()                { _, _ = os.Open(envSource()) }
func PositivePathOSOpenFile()            { _, _ = os.OpenFile(envSource(), os.O_RDONLY, 0600) }
func PositivePathOSCreate()              { _, _ = os.Create(envSource()) }
func PositivePathOSCreateTempDir()       { _, _ = os.CreateTemp(envSource(), "p") }
func PositivePathOSCreateTempPattern()   { _, _ = os.CreateTemp("", envSource()) }
func PositivePathOSMkdirTempDir()        { _, _ = os.MkdirTemp(envSource(), "p") }
func PositivePathOSMkdirTempPattern()    { _, _ = os.MkdirTemp("", envSource()) }
func PositivePathOSMkdir()               { _ = os.Mkdir(envSource(), 0700) }
func PositivePathOSMkdirAll()            { _ = os.MkdirAll(envSource(), 0700) }
func PositivePathOSRemove()              { _ = os.Remove(envSource()) }
func PositivePathOSRemoveAll()           { _ = os.RemoveAll(envSource()) }
func PositivePathOSReadFile()            { _, _ = os.ReadFile(envSource()) }
func PositivePathOSWriteFile()           { _ = os.WriteFile(envSource(), []byte("x"), 0600) }
func PositivePathOSReadDir()             { _, _ = os.ReadDir(envSource()) }
func PositivePathOSStat()                { _, _ = os.Stat(envSource()) }
func PositivePathOSLstat()               { _, _ = os.Lstat(envSource()) }
func PositivePathOSTruncate()            { _ = os.Truncate(envSource(), 1) }
func PositivePathOSChdir()               { _ = os.Chdir(envSource()) }
func PositivePathOSChmod()               { _ = os.Chmod(envSource(), 0600) }
func PositivePathOSChown()               { _ = os.Chown(envSource(), 1, 1) }
func PositivePathOSLchown()              { _ = os.Lchown(envSource(), 1, 1) }
func PositivePathOSChtimes()             { _ = os.Chtimes(envSource(), time.Unix(1, 0), time.Unix(1, 0)) }
func PositivePathOSReadlink()            { _, _ = os.Readlink(envSource()) }
func PositivePathOSRenameSource()        { _ = os.Rename(envSource(), "safe") }
func PositivePathOSRenameTarget()        { _ = os.Rename("safe", envSource()) }
func PositivePathOSLinkSource()          { _ = os.Link(envSource(), "safe") }
func PositivePathOSLinkTarget()          { _ = os.Link("safe", envSource()) }
func PositivePathOSSymlinkSource()       { _ = os.Symlink(envSource(), "safe") }
func PositivePathOSSymlinkTarget()       { _ = os.Symlink("safe", envSource()) }
func PositivePathOSDirFS()               { _ = os.DirFS(envSource()) }
func PositivePathIoutilReadFile()        { _, _ = ioutil.ReadFile(envSource()) }
func PositivePathIoutilWriteFile()       { _ = ioutil.WriteFile(envSource(), []byte("x"), 0600) }
func PositivePathIoutilReadDir()         { _, _ = ioutil.ReadDir(envSource()) }
func PositivePathIoutilTempFileDir()     { _, _ = ioutil.TempFile(envSource(), "p") }
func PositivePathIoutilTempFilePattern() { _, _ = ioutil.TempFile("", envSource()) }
func PositivePathIoutilTempDirDir()      { _, _ = ioutil.TempDir(envSource(), "p") }
func PositivePathIoutilTempDirPattern()  { _, _ = ioutil.TempDir("", envSource()) }
func PositivePathHTTPServeFile() {
	r := requestForSources()
	http.ServeFile(responseWriterWithString{}, r, envSource())
}

func PositiveSSRFHTTPGet()      { _, _ = http.Get(envSource()) }
func PositiveSSRFHTTPHead()     { _, _ = http.Head(envSource()) }
func PositiveSSRFHTTPPost()     { _, _ = http.Post(envSource(), "text/plain", strings.NewReader("x")) }
func PositiveSSRFHTTPPostForm() { _, _ = http.PostForm(envSource(), url.Values{"q": []string{"v"}}) }
func PositiveSSRFClientGet()    { _, _ = client.Get(envSource()) }
func PositiveSSRFClientHead()   { _, _ = client.Head(envSource()) }
func PositiveSSRFClientPost()   { _, _ = client.Post(envSource(), "text/plain", strings.NewReader("x")) }
func PositiveSSRFClientPostForm() {
	_, _ = client.PostForm(envSource(), url.Values{"q": []string{"v"}})
}
func PositiveSSRFNewRequest() { _, _ = http.NewRequest(http.MethodGet, envSource(), nil) }
func PositiveSSRFNewRequestWithContext() {
	_, _ = http.NewRequestWithContext(ctx, http.MethodGet, envSource(), nil)
}

func PositiveSSTITemplateParse()      { _, _ = template.New("x").Parse(envSource()) }
func PositiveSSTITemplateMustParse()  { _ = template.Must(template.New("x").Parse(envSource())) }
func PositiveSSTITemplateParseFiles() { _, _ = template.New("x").ParseFiles(envSource()) }
func PositiveSSTITemplateParseGlob()  { _, _ = template.New("x").ParseGlob(envSource()) }

func PositiveXSSWrite()         { _, _ = responseWriterWithString{}.Write([]byte(envSource())) }
func PositiveXSSWriteString()   { _, _ = responseWriterWithString{}.WriteString(envSource()) }
func PositiveXSSBody()          { beegoOutput{}.Body(envSource()) }
func PositiveXSSFprint()        { _, _ = fmt.Fprint(responseWriterWithString{}, envSource()) }
func PositiveXSSFprintf()       { _, _ = fmt.Fprintf(responseWriterWithString{}, "%s", envSource()) }
func PositiveXSSFprintln()      { _, _ = fmt.Fprintln(responseWriterWithString{}, envSource()) }
func PositiveXSSIOWriteString() { _, _ = io.WriteString(responseWriterWithString{}, envSource()) }
func PositiveXSSJSONEncoderEncode() {
	_ = json.NewEncoder(responseWriterWithString{}).Encode(envSource())
}
func PositiveXSSServeJSON()  { c := &jsonController{Data: envSource()}; c.ServeJSON() }
func PositiveXSSOutputJSON() { beegoOutput{}.JSON(envSource(), 200) }

func NegativeXSSHTMLEscapeString() {
	_, _ = responseWriterWithString{}.WriteString(template.HTMLEscapeString(envSource()))
}
func NegativeXSSJSEscapeString() {
	_, _ = responseWriterWithString{}.WriteString(template.JSEscapeString(envSource()))
}
func UnsupportedNegativeXSSURLQueryEscaper() {
	_, _ = responseWriterWithString{}.WriteString(template.URLQueryEscaper(envSource()))
}
func UnsupportedNegativeXSSHTMLEscaper() {
	_, _ = responseWriterWithString{}.WriteString(template.HTMLEscaper(envSource()))
}
func NegativeXSSHTMLEscape() {
	_, _ = responseWriterWithString{}.WriteString(html.EscapeString(envSource()))
}
func NegativeXSSURLQueryEscape() {
	_, _ = responseWriterWithString{}.WriteString(url.QueryEscape(envSource()))
}
func NegativeXSSURLPathEscape() {
	_, _ = responseWriterWithString{}.WriteString(url.PathEscape(envSource()))
}

func PositiveTrustSetCookie()  { http.SetCookie(responseWriterWithString{}, cookieFrom(envSource())) }
func PositiveTrustSetSession() { c := &web.Controller{}; _ = c.SetSession("q", envSource()) }

func PositiveWeakCryptoDES()                { _, _ = des.NewCipher([]byte("12345678")) }
func PositiveWeakCryptoTripleDES()          { _, _ = des.NewTripleDESCipher([]byte("123456789012345678901234")) }
func PositiveWeakCryptoRC4()                { _, _ = rc4.NewCipher([]byte("secret")) }
func PositiveWeakCryptoMD4()                { _ = md4.New() }
func PositiveWeakCryptoCipherECBEncrypter() { _ = cipher.NewECBEncrypter("block") }
func PositiveWeakCryptoCipherECBDecrypter() { _ = cipher.NewECBDecrypter("block") }
func PositiveWeakCryptoECBEncrypter()       { _ = NewECBEncrypter("block") }
func PositiveWeakCryptoECBDecrypter()       { _ = NewECBDecrypter("block") }

func NewECBEncrypter(args ...interface{}) interface{} { return args }
func NewECBDecrypter(args ...interface{}) interface{} { return args }

func PositiveWeakHashMD5New()  { _ = md5.New() }
func PositiveWeakHashMD5Sum()  { _ = md5.Sum([]byte("x")) }
func PositiveWeakHashSHA1New() { _ = sha1.New() }
func PositiveWeakHashSHA1Sum() { _ = sha1.Sum([]byte("x")) }
func PositiveWeakHashMD4New()  { _ = md4.New() }

func PositiveWeakRandomInt()         { _ = rand.Int() }
func PositiveWeakRandomIntn()        { _ = rand.Intn(10) }
func PositiveWeakRandomInt31()       { _ = rand.Int31() }
func PositiveWeakRandomInt31n()      { _ = rand.Int31n(10) }
func PositiveWeakRandomInt63()       { _ = rand.Int63() }
func PositiveWeakRandomInt63n()      { _ = rand.Int63n(10) }
func PositiveWeakRandomFloat64()     { _ = rand.Float64() }
func PositiveWeakRandomFloat32()     { _ = rand.Float32() }
func PositiveWeakRandomNormFloat64() { _ = rand.NormFloat64() }
func PositiveWeakRandomExpFloat64()  { _ = rand.ExpFloat64() }
func PositiveWeakRandomUint32()      { _ = rand.Uint32() }
func PositiveWeakRandomUint64()      { _ = rand.Uint64() }
func PositiveWeakRandomPerm()        { _ = rand.Perm(10) }
func PositiveWeakRandomNew()         { _ = rand.New(rand.NewSource(1)) }
