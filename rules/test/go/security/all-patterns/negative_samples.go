package allpatterns

import (
	"crypto/aes"
	cryptorand "crypto/rand"
	"crypto/sha256"
	"math/big"
	"net/http"
	"os"
	"os/exec"
)

func NegativeSourceUnusedFormValue() {
	r := requestForSources()
	_ = r.FormValue("q")
}

func NegativeSQLConstantQuery() {
	_, _ = db.Query("select * from users where active = 1")
}

func NegativeCmdConstantCommand() {
	_ = exec.Command("ls", "-la").Run()
}

func NegativeCmdSafeArgv() {
	_ = exec.Command("echo", envSource())
}

func NegativePathConstantPath() {
	_, _ = os.Open("/etc/app/config.yaml")
}

func NegativeSSRFConstantURL() {
	_, _ = http.Get("https://api.internal.example/health")
}

func NegativeTrustConstantCookie() {
	http.SetCookie(xssResponseWriter(), &http.Cookie{Name: "session", Value: "constant"})
}

func NegativeWeakHashSHA256New() {
	_ = sha256.New()
}

func NegativeWeakHashSHA256Sum() {
	_ = sha256.Sum256([]byte("payload"))
}

func NegativeWeakCryptoAES() {
	_, _ = aes.NewCipher([]byte("0123456789abcdef"))
}

func NegativeWeakRandomCryptoInt() {
	_, _ = cryptorand.Int(cryptorand.Reader, big.NewInt(10))
}

func NegativeWeakRandomCryptoRead() {
	_, _ = cryptorand.Read(make([]byte, 16))
}
