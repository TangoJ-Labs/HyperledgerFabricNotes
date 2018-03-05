/*
Copyright IBM Corp. 2017 All Rights Reserved.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
		 http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/
package main //custom-hl

import (
    "bytes"
    "crypto"
    "crypto/aes"
    "crypto/cipher"
    "crypto/ecdsa"
    "crypto/elliptic"
    "crypto/hmac"
    "crypto/rand"
    "crypto/rsa"
    "crypto/sha256"
    "crypto/sha512"
    "crypto/x509"
    "crypto/x509/pkix"
    "encoding/asn1"
    "encoding/hex"
    "encoding/pem"
    "errors"
    "fmt"
    "hash"
    "io"
    "io/ioutil"
    "math/big"
    "os"
    "path/filepath"
    "reflect"
    "regexp"
    "runtime"
    "strings"
    "sync"
    "text/template"
    "time"

    "golang.org/x/crypto/sha3"

    "gopkg.in/yaml.v2"
    "gopkg.in/alecthomas/kingpin.v2"

    "github.com/op/go-logging"
    "github.com/miekg/pkcs11"

    // "github.com/hyperledger/fabric/common/tools/cryptogen/ca"
    // "github.com/hyperledger/fabric/common/tools/cryptogen/metadata"
    // "github.com/hyperledger/fabric/common/tools/cryptogen/msp"
)



/*** hyperledger-mod/fabric/common/errors/errors.go ***/
// MaxCallStackLength is the maximum length of the stored call stack
const MaxCallStackLength = 30
var (
	componentPattern = "[A-Za-z]{3}"
	reasonPattern    = "[0-9]{3}"
)

/*** hyperledger-mod/fabric/bccsp/sw/impl.go ***/
var (
	logger = MustGetLogger("bccsp_sw") //SOURCE:flogging.MustGetLogger
)

/*** hyperledger/fabric/common/flogging/logging.go ***/
var (
	modules map[string]string // Holds the map of all modules and their respective log level
	lock sync.RWMutex
)
// GetModuleLevel gets the current logging level for the specified module.
func GetModuleLevel(module string) string {
	// logging.GetLevel() returns the logging level for the module, if defined.
	// Otherwise, it returns the default logging level, as set by
	// `flogging/logging.go`.
	level := logging.GetLevel(module).String()
	return level
}
// MustGetLogger is used in place of `logging.MustGetLogger` to allow us to
// store a map of all modules and submodules that have loggers in the system.
func MustGetLogger(module string) *logging.Logger {
    modules = make(map[string]string)
    lock = sync.RWMutex{}
	l := logging.MustGetLogger(module)
	lock.Lock()
	defer lock.Unlock()
	modules[module] = GetModuleLevel(module)
	return l
}

/*** hyperledger-mod/fabric/common/errors/errors.go ***/
func (e *callError) setErrorFields(componentcode string, reasoncode string, message string, args ...interface{}) {
	if isValidComponentOrReasonCode(componentcode, componentPattern) {
		e.componentcode = componentcode
	}
	if isValidComponentOrReasonCode(reasoncode, reasonPattern) {
		e.reasoncode = reasoncode
	}
	if message != "" {
		e.message = message
	}
	e.args = args
}
func isValidComponentOrReasonCode(componentOrReasonCode string, regExp string) bool {
	if componentOrReasonCode == "" {
		return false
	}
	re, _ := regexp.Compile(regExp)
	matched := re.FindString(componentOrReasonCode)
	if len(matched) != len(componentOrReasonCode) {
		return false
	}
	return true
}

/*** hyperledger-mod/fabric/common/errors/codes.go ***/
// A set of constants for error reason codes, which is based on HTTP codes
// http://www.iana.org/assignments/http-status-codes/http-status-codes.xhtml
const (
	// Invalid inputs on API calls
	BadRequest = "400"

	// Not Found (eg chaincode not found)
	NotFound = "404"

	// Internal server errors that are not classified below
	Internal = "500"
)
// A set of constants for component codes
const (
	// BCCSP is fabic/BCCSP
	BCCSP_const = "CSP" //WAS "BCCSP"
)

/*** hyperledger-mod/fabric/common/errors/errors.go ***/
// Error comes from the error interface - it returns the error message and
// appends the callstack, if available
func (e *callError) Error() string {
	message := e.GetErrorCode() + " - " + fmt.Sprintf(e.message, e.args...)
	// check that the error has a callstack before proceeding
	if e.GetStack() != "" {
		message = appendCallStack(message, e.GetStack())
	}
	if e.prevErr != nil {
		message += "\nCaused by: " + e.prevErr.Error()
	}
	return message
}
// GetStack returns the call stack as a string
func (e *callError) GetStack() string {
	return e.stackGetter(e.stack)
}
// GetComponentCode returns the component name
func (e *callError) GetComponentCode() string {
	return e.componentcode
}
// GetReasonCode returns the reason code - i.e. why the error occurred
func (e *callError) GetReasonCode() string {
	return e.reasoncode
}
// GetErrorCode returns a formatted error code string
func (e *callError) GetErrorCode() string {
	return fmt.Sprintf("%s:%s", e.componentcode, e.reasoncode)
}
// Message returns the corresponding error message for this error in default
// language.
func (e *callError) Message() string {
	message := e.GetErrorCode() + " - " + fmt.Sprintf(e.message, e.args...)

	if e.prevErr != nil {
		switch previousError := e.prevErr.(type) {
		case CallStackError:
			message += "\nCaused by: " + previousError.Message()
		default:
			message += "\nCaused by: " + e.prevErr.Error()
		}
	}
	return message
}
func appendCallStack(message string, callstack string) string {
	return message + "\n" + callstack
}
// GenerateStack generates the callstack for a CallStackError
func (e *callError) GenerateStack(flag bool) CallStackError {
	setupCallError(e, flag)
	return e
}
// WrapError wraps a previous error into a CallStackError
func (e *callError) WrapError(prevErr error) CallStackError {
	e.prevErr = prevErr
	return e
}
func getStack(stack callstack) string {
	buf := bytes.Buffer{}
	if stack == nil {
		return fmt.Sprintf("No call stack available")
	}
	// this removes the core/errors module calls from the callstack because they
	// are not useful for debugging
	const firstNonErrorModuleCall int = 2
	stack = stack[firstNonErrorModuleCall:]
	for i, pc := range stack {
		f := runtime.FuncForPC(pc)
		file, line := f.FileLine(pc)
		if i != len(stack)-1 {
			buf.WriteString(fmt.Sprintf("%s:%d %s\n", file, line, f.Name()))
		} else {
			buf.WriteString(fmt.Sprintf("%s:%d %s", file, line, f.Name()))
		}
	}
	return fmt.Sprintf("%s", buf.Bytes())
}
func noopGetStack(stack callstack) string {
	return ""
}

/*** hyperledger-mod/fabric/common/errors/errors.go ***/
// CallStackError is a general interface for Fabric errors
type CallStackError interface {
	error
	GetStack() string
	GetErrorCode() string
	GetComponentCode() string
	GetReasonCode() string
	Message() string
	GenerateStack(bool) CallStackError
	WrapError(error) CallStackError
}
type callstack []uintptr
// callError is the 'super class' of all errors
type callError struct {
	stack         callstack
	componentcode string
	reasoncode    string
	message       string
	args          []interface{}
	stackGetter   func(callstack) string
	prevErr       error
}
func setupCallError(e *callError, generateStack bool) {
	if !generateStack {
		e.stackGetter = noopGetStack
		return
	}
	e.stackGetter = getStack
	stack := make([]uintptr, MaxCallStackLength)
	skipCallersAndSetup := 2
	length := runtime.Callers(skipCallersAndSetup, stack[:])
	e.stack = stack[:length]
}

/*** hyperledger-mod/fabric/common/errors/errors.go ***/
// ErrorWithCallstack creates a CallStackError using a specific component code
// and reason code and generates its callstack
func ErrorWithCallstack(componentcode string, reasoncode string, message string, args ...interface{}) CallStackError {
	return newError(componentcode, reasoncode, message, args...).GenerateStack(true)
}
func newError(componentcode string, reasoncode string, message string, args ...interface{}) CallStackError {
	e := &callError{}
	e.setErrorFields(componentcode, reasoncode, message, args...)
	return e
}

/*** hyperledger-mod/fabric/bccsp/sw/rsa.go ***/
type rsaSigner struct{}
func (s *rsaSigner) Sign(k Key, digest []byte, opts SignerOpts) (signature []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	if opts == nil {
		return nil, errors.New("Invalid options. Must be different from nil.")
	}

	return k.(*rsaPrivateKey).privKey.Sign(rand.Reader, digest, opts)
}
type rsaPrivateKeyVerifier struct{}
func (v *rsaPrivateKeyVerifier) Verify(k Key, signature, digest []byte, opts SignerOpts) (valid bool, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	if opts == nil {
		return false, errors.New("Invalid options. It must not be nil.")
	}
	switch opts.(type) {
	case *rsa.PSSOptions:
		err := rsa.VerifyPSS(&(k.(*rsaPrivateKey).privKey.PublicKey),
			(opts.(*rsa.PSSOptions)).Hash,
			digest, signature, opts.(*rsa.PSSOptions))

		return err == nil, err
	default:
		return false, fmt.Errorf("Opts type not recognized [%s]", opts)
	}
}
type rsaPublicKeyKeyVerifier struct{}
func (v *rsaPublicKeyKeyVerifier) Verify(k Key, signature, digest []byte, opts SignerOpts) (valid bool, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	if opts == nil {
		return false, errors.New("Invalid options. It must not be nil.")
	}
	switch opts.(type) {
	case *rsa.PSSOptions:
		err := rsa.VerifyPSS(k.(*rsaPublicKey).pubKey,
			(opts.(*rsa.PSSOptions)).Hash,
			digest, signature, opts.(*rsa.PSSOptions))

		return err == nil, err
	default:
		return false, fmt.Errorf("Opts type not recognized [%s]", opts)
	}
}

/*** hyperledger-mod/fabric/bccsp/sw/conf.go ***/
type config struct {
	ellipticCurve elliptic.Curve
	hashFunction  func() hash.Hash
	aesBitLength  int
	rsaBitLength  int
}
func (conf *config) setSecurityLevel(securityLevel int, hashFamily string) (err error) {
	switch hashFamily {
	case "SHA2":
		err = conf.setSecurityLevelSHA2(securityLevel)
	case "SHA3":
		err = conf.setSecurityLevelSHA3(securityLevel)
	default:
		err = fmt.Errorf("Hash Family not supported [%s]", hashFamily)
	}
	return
}
func (conf *config) setSecurityLevelSHA2(level int) (err error) {
	switch level {
	case 256:
		conf.ellipticCurve = elliptic.P256()
		conf.hashFunction = sha256.New
		conf.rsaBitLength = 2048
		conf.aesBitLength = 32
	case 384:
		conf.ellipticCurve = elliptic.P384()
		conf.hashFunction = sha512.New384
		conf.rsaBitLength = 3072
		conf.aesBitLength = 32
	default:
		err = fmt.Errorf("Security level not supported [%d]", level)
	}
	return
}
func (conf *config) setSecurityLevelSHA3(level int) (err error) {
	switch level {
	case 256:
		conf.ellipticCurve = elliptic.P256()
		conf.hashFunction = sha3.New256
		conf.rsaBitLength = 2048
		conf.aesBitLength = 32
	case 384:
		conf.ellipticCurve = elliptic.P384()
		conf.hashFunction = sha3.New384
		conf.rsaBitLength = 3072
		conf.aesBitLength = 32
	default:
		err = fmt.Errorf("Security level not supported [%d]", level)
	}
	return
}

/*** hyperledger-mod/fabric/bccsp/sw/rsakey.go ***/
// rsaPublicKey reflects the ASN.1 structure of a PKCS#1 public key.
type rsaPublicKeyASN struct {
	N *big.Int
	E int
}
type rsaPrivateKey struct {
	privKey *rsa.PrivateKey
}
// Bytes converts this key to its byte representation,
// if this operation is allowed.
func (k *rsaPrivateKey) Bytes() (raw []byte, err error) {
	return nil, errors.New("Not supported.")
}
// SKI returns the subject key identifier of this key.
func (k *rsaPrivateKey) SKI() (ski []byte) {
	if k.privKey == nil {
		return nil
	}

	// Marshall the public key
	raw, _ := asn1.Marshal(rsaPublicKeyASN{
		N: k.privKey.N,
		E: k.privKey.E,
	})

	// Hash it
	hash := sha256.New()
	hash.Write(raw)
	return hash.Sum(nil)
}
// Symmetric returns true if this key is a symmetric key,
// false is this key is asymmetric
func (k *rsaPrivateKey) Symmetric() bool {
	return false
}
// Private returns true if this key is an asymmetric private key,
// false otherwise.
func (k *rsaPrivateKey) Private() bool {
	return true
}
// PublicKey returns the corresponding public key part of an asymmetric public/private key pair.
// This method returns an error in symmetric key schemes.
func (k *rsaPrivateKey) PublicKey() (Key, error) { //SOURCE:bccsp.Key
	return &rsaPublicKey{&k.privKey.PublicKey}, nil
}
type rsaPublicKey struct {
	pubKey *rsa.PublicKey
}
// Bytes converts this key to its byte representation,
// if this operation is allowed.
func (k *rsaPublicKey) Bytes() (raw []byte, err error) {
	if k.pubKey == nil {
		return nil, errors.New("Failed marshalling key. Key is nil.")
	}
	raw, err = x509.MarshalPKIXPublicKey(k.pubKey)
	if err != nil {
		return nil, fmt.Errorf("Failed marshalling key [%s]", err)
	}
	return
}
// SKI returns the subject key identifier of this key.
func (k *rsaPublicKey) SKI() (ski []byte) {
	if k.pubKey == nil {
		return nil
	}

	// Marshall the public key
	raw, _ := asn1.Marshal(rsaPublicKeyASN{
		N: k.pubKey.N,
		E: k.pubKey.E,
	})

	// Hash it
	hash := sha256.New()
	hash.Write(raw)
	return hash.Sum(nil)
}
// Symmetric returns true if this key is a symmetric key,
// false is this key is asymmetric
func (k *rsaPublicKey) Symmetric() bool {
	return false
}
// Private returns true if this key is an asymmetric private key,
// false otherwise.
func (k *rsaPublicKey) Private() bool {
	return false
}
// PublicKey returns the corresponding public key part of an asymmetric public/private key pair.
// This method returns an error in symmetric key schemes.
func (k *rsaPublicKey) PublicKey() (Key, error) { //SOURCE:bccsp.Key
	return k, nil
}

/*** hyperledger-mod/fabric/bccsp/sw/ecdsa.go ***/
var (
	// curveHalfOrders contains the precomputed curve group orders halved.
	// It is used to ensure that signature' S value is lower or equal to the
	// curve group order halved. We accept only low-S signatures.
	// They are precomputed for efficiency reasons.
	curveHalfOrders map[elliptic.Curve]*big.Int = map[elliptic.Curve]*big.Int{
		elliptic.P224(): new(big.Int).Rsh(elliptic.P224().Params().N, 1),
		elliptic.P256(): new(big.Int).Rsh(elliptic.P256().Params().N, 1),
		elliptic.P384(): new(big.Int).Rsh(elliptic.P384().Params().N, 1),
		elliptic.P521(): new(big.Int).Rsh(elliptic.P521().Params().N, 1),
	}
)
type ecdsaSigner struct{}
func (s *ecdsaSigner) Sign(k Key, digest []byte, opts SignerOpts) (signature []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	return signECDSA(k.(*ecdsaPrivateKey).privKey, digest, opts)
}
func signECDSA(k *ecdsa.PrivateKey, digest []byte, opts SignerOpts) (signature []byte, err error) { //SOURCE:bccsp.SignerOpts
	r, s, err := ecdsa.Sign(rand.Reader, k, digest)
	if err != nil {
		return nil, err
	}

	s, _, err = ToLowS(&k.PublicKey, s)
	if err != nil {
		return nil, err
	}

	return MarshalECDSASignature(r, s)
}
type ECDSASignature struct {
	R, S *big.Int
}
func MarshalECDSASignature(r, s *big.Int) ([]byte, error) {
	return asn1.Marshal(ECDSASignature{r, s})
}
func UnmarshalECDSASignature(raw []byte) (*big.Int, *big.Int, error) {
	// Unmarshal
	sig := new(ECDSASignature)
	_, err := asn1.Unmarshal(raw, sig)
	if err != nil {
		return nil, nil, fmt.Errorf("Failed unmashalling signature [%s]", err)
	}

	// Validate sig
	if sig.R == nil {
		return nil, nil, errors.New("Invalid signature. R must be different from nil.")
	}
	if sig.S == nil {
		return nil, nil, errors.New("Invalid signature. S must be different from nil.")
	}

	if sig.R.Sign() != 1 {
		return nil, nil, errors.New("Invalid signature. R must be larger than zero")
	}
	if sig.S.Sign() != 1 {
		return nil, nil, errors.New("Invalid signature. S must be larger than zero")
	}

	return sig.R, sig.S, nil
}
func ToLowS(k *ecdsa.PublicKey, s *big.Int) (*big.Int, bool, error) {
	lowS, err := IsLowS(k, s)
	if err != nil {
		return nil, false, err
	}

	if !lowS {
		// Set s to N - s that will be then in the lower part of signature space
		// less or equal to half order
		s.Sub(k.Params().N, s)

		return s, true, nil
	}

	return s, false, nil
}
func IsLowS(k *ecdsa.PublicKey, s *big.Int) (bool, error) {
	halfOrder, ok := curveHalfOrders[k.Curve]
	if !ok {
		return false, fmt.Errorf("Curve not recognized [%s]", k.Curve)
	}

	return s.Cmp(halfOrder) != 1, nil

}
func verifyECDSA(k *ecdsa.PublicKey, signature, digest []byte, opts SignerOpts) (valid bool, err error) { //SOURCE:bccsp.SignerOpts
	r, s, err := UnmarshalECDSASignature(signature)
	if err != nil {
		return false, fmt.Errorf("Failed unmashalling signature [%s]", err)
	}

	lowS, err := IsLowS(k, s)
	if err != nil {
		return false, err
	}

	if !lowS {
		return false, fmt.Errorf("Invalid S. Must be smaller than half the order [%s][%s].", s, curveHalfOrders[k.Curve])
	}

	return ecdsa.Verify(k, digest, r, s), nil
}
type ecdsaPrivateKeyVerifier struct{}
func (v *ecdsaPrivateKeyVerifier) Verify(k Key, signature, digest []byte, opts SignerOpts) (valid bool, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	return verifyECDSA(&(k.(*ecdsaPrivateKey).privKey.PublicKey), signature, digest, opts)
}
type ecdsaPublicKeyKeyVerifier struct{}
func (v *ecdsaPublicKeyKeyVerifier) Verify(k Key, signature, digest []byte, opts SignerOpts) (valid bool, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	return verifyECDSA(k.(*ecdsaPublicKey).pubKey, signature, digest, opts)
}

/*** hyperledger-mod/fabric/bccsp/sw/ecdsakey.go ***/
type ecdsaPrivateKey struct {
	privKey *ecdsa.PrivateKey
}
// Bytes converts this key to its byte representation,
// if this operation is allowed.
func (k *ecdsaPrivateKey) Bytes() (raw []byte, err error) {
	return nil, errors.New("Not supported.")
}
// SKI returns the subject key identifier of this key.
func (k *ecdsaPrivateKey) SKI() (ski []byte) {
	if k.privKey == nil {
		return nil
	}

	// Marshall the public key
	raw := elliptic.Marshal(k.privKey.Curve, k.privKey.PublicKey.X, k.privKey.PublicKey.Y)

	// Hash it
	hash := sha256.New()
	hash.Write(raw)
	return hash.Sum(nil)
}
// Symmetric returns true if this key is a symmetric key,
// false if this key is asymmetric
func (k *ecdsaPrivateKey) Symmetric() bool {
	return false
}
// Private returns true if this key is a private key,
// false otherwise.
func (k *ecdsaPrivateKey) Private() bool {
	return true
}
// PublicKey returns the corresponding public key part of an asymmetric public/private key pair.
// This method returns an error in symmetric key schemes.
func (k *ecdsaPrivateKey) PublicKey() (Key, error) { //SOURCE:bccsp.Key
	return &ecdsaPublicKey{&k.privKey.PublicKey}, nil
}
type ecdsaPublicKey struct {
	pubKey *ecdsa.PublicKey
}
// Bytes converts this key to its byte representation,
// if this operation is allowed.
func (k *ecdsaPublicKey) Bytes() (raw []byte, err error) {
	raw, err = x509.MarshalPKIXPublicKey(k.pubKey)
	if err != nil {
		return nil, fmt.Errorf("Failed marshalling key [%s]", err)
	}
	return
}
// SKI returns the subject key identifier of this key.
func (k *ecdsaPublicKey) SKI() (ski []byte) {
	if k.pubKey == nil {
		return nil
	}

	// Marshall the public key
	raw := elliptic.Marshal(k.pubKey.Curve, k.pubKey.X, k.pubKey.Y)

	// Hash it
	hash := sha256.New()
	hash.Write(raw)
	return hash.Sum(nil)
}
// Symmetric returns true if this key is a symmetric key,
// false if this key is asymmetric
func (k *ecdsaPublicKey) Symmetric() bool {
	return false
}
// Private returns true if this key is a private key,
// false otherwise.
func (k *ecdsaPublicKey) Private() bool {
	return false
}
// PublicKey returns the corresponding public key part of an asymmetric public/private key pair.
// This method returns an error in symmetric key schemes.
func (k *ecdsaPublicKey) PublicKey() (Key, error) { //SOURCE:bccsp.Key
	return k, nil
}

/*** hyperledger-mod/fabric/bccsp/opts.go ***/
// AESCBCPKCS7ModeOpts contains options for AES encryption in CBC mode
// with PKCS7 padding.
type AESCBCPKCS7ModeOpts struct{}

/*** hyperledger-mod/fabric/bccsp/sw/aes.go ***/
type aescbcpkcs7Encryptor struct{}
func (*aescbcpkcs7Encryptor) Encrypt(k Key, plaintext []byte, opts EncrypterOpts) (ciphertext []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.EncrypterOpts
	switch opts.(type) {
	case *AESCBCPKCS7ModeOpts, AESCBCPKCS7ModeOpts: //SOURCE:bccsp.AESCBCPKCS7ModeOpts
		// AES in CBC mode with PKCS7 padding
		return AESCBCPKCS7Encrypt(k.(*aesPrivateKey).privKey, plaintext)
	default:
		return nil, fmt.Errorf("Mode not recognized [%s]", opts)
	}
}
func AESCBCPKCS7Encrypt(key, src []byte) ([]byte, error) {
	// First pad
	tmp := pkcs7Padding(src)

	// Then encrypt
	return aesCBCEncrypt(key, tmp)
}
func pkcs7Padding(src []byte) []byte {
	padding := aes.BlockSize - len(src)%aes.BlockSize
	padtext := bytes.Repeat([]byte{byte(padding)}, padding)
	return append(src, padtext...)
}
func aesCBCEncrypt(key, s []byte) ([]byte, error) {
	if len(s)%aes.BlockSize != 0 {
		return nil, errors.New("Invalid plaintext. It must be a multiple of the block size")
	}

	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, err
	}

	ciphertext := make([]byte, aes.BlockSize+len(s))
	iv := ciphertext[:aes.BlockSize]
	if _, err := io.ReadFull(rand.Reader, iv); err != nil {
		return nil, err
	}

	mode := cipher.NewCBCEncrypter(block, iv)
	mode.CryptBlocks(ciphertext[aes.BlockSize:], s)

	return ciphertext, nil
}
type aescbcpkcs7Decryptor struct{}
func (*aescbcpkcs7Decryptor) Decrypt(k Key, ciphertext []byte, opts DecrypterOpts) (plaintext []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.DecrypterOpts
	// check for mode
	switch opts.(type) {
	case *AESCBCPKCS7ModeOpts, AESCBCPKCS7ModeOpts: //SOURCE:bccsp.AESCBCPKCS7ModeOpts
		// AES in CBC mode with PKCS7 padding
		return AESCBCPKCS7Decrypt(k.(*aesPrivateKey).privKey, ciphertext)
	default:
		return nil, fmt.Errorf("Mode not recognized [%s]", opts)
	}
}
func AESCBCPKCS7Decrypt(key, src []byte) ([]byte, error) {
	// First decrypt
	pt, err := aesCBCDecrypt(key, src)
	if err == nil {
		return pkcs7UnPadding(pt)
	}
	return nil, err
}
func pkcs7UnPadding(src []byte) ([]byte, error) {
	length := len(src)
	unpadding := int(src[length-1])

	if unpadding > aes.BlockSize || unpadding == 0 {
		return nil, errors.New("Invalid pkcs7 padding (unpadding > aes.BlockSize || unpadding == 0)")
	}

	pad := src[len(src)-unpadding:]
	for i := 0; i < unpadding; i++ {
		if pad[i] != byte(unpadding) {
			return nil, errors.New("Invalid pkcs7 padding (pad[i] != unpadding)")
		}
	}

	return src[:(length - unpadding)], nil
}
func aesCBCDecrypt(key, src []byte) ([]byte, error) {
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, err
	}

	if len(src) < aes.BlockSize {
		return nil, errors.New("Invalid ciphertext. It must be a multiple of the block size")
	}
	iv := src[:aes.BlockSize]
	src = src[aes.BlockSize:]

	if len(src)%aes.BlockSize != 0 {
		return nil, errors.New("Invalid ciphertext. It must be a multiple of the block size")
	}

	mode := cipher.NewCBCDecrypter(block, iv)

	mode.CryptBlocks(src, src)

	return src, nil
}

/*** hyperledger-mod/fabric/bccsp/sw/aeskey.go ***/
type aesPrivateKey struct {
	privKey    []byte
	exportable bool
}
// Bytes converts this key to its byte representation,
// if this operation is allowed.
func (k *aesPrivateKey) Bytes() (raw []byte, err error) {
	if k.exportable {
		return k.privKey, nil
	}

	return nil, errors.New("Not supported.")
}
// SKI returns the subject key identifier of this key.
func (k *aesPrivateKey) SKI() (ski []byte) {
	hash := sha256.New()
	hash.Write([]byte{0x01})
	hash.Write(k.privKey)
	return hash.Sum(nil)
}
// Symmetric returns true if this key is a symmetric key,
// false if this key is asymmetric
func (k *aesPrivateKey) Symmetric() bool {
	return true
}
// Private returns true if this key is a private key,
// false otherwise.
func (k *aesPrivateKey) Private() bool {
	return true
}
// PublicKey returns the corresponding public key part of an asymmetric public/private key pair.
// This method returns an error in symmetric key schemes.
func (k *aesPrivateKey) PublicKey() (Key, error) { //SOURCE:bccsp.Key
	return nil, errors.New("Cannot call this method on a symmetric key.")
}

/*** hyperledger-mod/fabric/bccsp/sw/internals.go ***/
// KeyGenerator is a BCCSP-like interface that provides key generation algorithms
type KeyGenerator interface {

	// KeyGen generates a key using opts.
	KeyGen(opts KeyGenOpts) (k Key, err error) //SOURCE:bccsp.KeyGenOpts //SOURCE:bccsp.Key
}
// KeyDeriver is a BCCSP-like interface that provides key derivation algorithms
type KeyDeriver interface {

	// KeyDeriv derives a key from k using opts.
	// The opts argument should be appropriate for the primitive used.
	KeyDeriv(k Key, opts KeyDerivOpts) (dk Key, err error) //SOURCE:bccsp.Key //SOURCE:bccsp.KeyDerivOpts
}
// KeyImporter is a BCCSP-like interface that provides key import algorithms
type KeyImporter interface {

	// KeyImport imports a key from its raw representation using opts.
	// The opts argument should be appropriate for the primitive used.
	KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error) //SOURCE:bccsp.KeyImportOpts //SOURCE:bccsp.Key
}
// Encryptor is a BCCSP-like interface that provides encryption algorithms
type Encryptor interface {

	// Encrypt encrypts plaintext using key k.
	// The opts argument should be appropriate for the algorithm used.
	Encrypt(k Key, plaintext []byte, opts EncrypterOpts) (ciphertext []byte, err error) //SOURCE:bccsp.Key //SOURCE:bccsp.EncrypterOpts
}
// Decryptor is a BCCSP-like interface that provides decryption algorithms
type Decryptor interface {

	// Decrypt decrypts ciphertext using key k.
	// The opts argument should be appropriate for the algorithm used.
	Decrypt(k Key, ciphertext []byte, opts DecrypterOpts) (plaintext []byte, err error) //SOURCE:bccsp.Key //SOURCE:bccsp.DecrypterOpts
}
// Signer is a BCCSP-like interface that provides signing algorithms
type Signer interface {

	// Sign signs digest using key k.
	// The opts argument should be appropriate for the algorithm used.
	//
	// Note that when a signature of a hash of a larger message is needed,
	// the caller is responsible for hashing the larger message and passing
	// the hash (as digest).
	Sign(k Key, digest []byte, opts SignerOpts) (signature []byte, err error) //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
}
// Verifier is a BCCSP-like interface that provides verifying algorithms
type Verifier interface {

	// Verify verifies signature against key k and digest
	// The opts argument should be appropriate for the algorithm used.
	Verify(k Key, signature, digest []byte, opts SignerOpts) (valid bool, err error) //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
}
// Hasher is a BCCSP-like interface that provides hash algorithms
type Hasher interface {

	// Hash hashes messages msg using options opts.
	// If opts is nil, the default hash function will be used.
	Hash(msg []byte, opts HashOpts) (hash []byte, err error) //SOURCE:bccsp.HashOpts

	// GetHash returns and instance of hash.Hash using options opts.
	// If opts is nil, the default hash function will be returned.
	GetHash(opts HashOpts) (h hash.Hash, err error) //SOURCE:bccsp.HashOpts
}

/*** hyperledger-mod/fabric/bccsp/sw/hash.go ***/
type hasher struct {
	hash func() hash.Hash
}
func (c *hasher) Hash(msg []byte, opts HashOpts) (hash []byte, err error) { //SOURCE:bccsp.HashOpts
	h := c.hash()
	h.Write(msg)
	return h.Sum(nil), nil
}
func (c *hasher) GetHash(opts HashOpts) (h hash.Hash, err error) { //SOURCE:bccsp.HashOpts
	return c.hash(), nil
}

/*** hyperledger-mod/fabric/bccsp/opts.go ***/
// SHAOpts contains options for computing SHA.
type SHAOpts struct {}
// ECDSAKeyGenOpts contains options for ECDSA key generation.
type ECDSAKeyGenOpts struct {
	Temporary bool
}
// ECDSAReRandKeyOpts contains options for ECDSA key re-randomization.
type ECDSAReRandKeyOpts struct {
	Temporary bool
	Expansion []byte
}
// ECDSAReRand ECDSA key re-randomization
const ECDSAReRand = "ECDSA_RERAND"
// Algorithm returns the key derivation algorithm identifier (to be used).
func (opts *ECDSAReRandKeyOpts) Algorithm() string {
	return ECDSAReRand
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *ECDSAReRandKeyOpts) Ephemeral() bool {
	return opts.Temporary
}
// ExpansionValue returns the re-randomization factor
func (opts *ECDSAReRandKeyOpts) ExpansionValue() []byte {
	return opts.Expansion
}
// ECDSAPKIXPublicKeyImportOpts contains options for ECDSA public key importation in PKIX format
type ECDSAPKIXPublicKeyImportOpts struct {
	Temporary bool
}
// ECDSA Elliptic Curve Digital Signature Algorithm (key gen, import, sign, verify),
// at default security level.
// Each BCCSP may or may not support default security level. If not supported than
// an error will be returned.
const ECDSA = "ECDSA"
// Algorithm returns the key importation algorithm identifier (to be used).
func (opts *ECDSAPKIXPublicKeyImportOpts) Algorithm() string {
	return ECDSA
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *ECDSAPKIXPublicKeyImportOpts) Ephemeral() bool {
	return opts.Temporary
}
// ECDSAPrivateKeyImportOpts contains options for ECDSA secret key importation in DER format
// or PKCS#8 format.
type ECDSAPrivateKeyImportOpts struct {
	Temporary bool
}
// Algorithm returns the key importation algorithm identifier (to be used).
func (opts *ECDSAPrivateKeyImportOpts) Algorithm() string {
	return ECDSA
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *ECDSAPrivateKeyImportOpts) Ephemeral() bool {
	return opts.Temporary
}
// ECDSAGoPublicKeyImportOpts contains options for ECDSA key importation from ecdsa.PublicKey
type ECDSAGoPublicKeyImportOpts struct {
	Temporary bool
}
// Algorithm returns the key importation algorithm identifier (to be used).
func (opts *ECDSAGoPublicKeyImportOpts) Algorithm() string {
	return ECDSA
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *ECDSAGoPublicKeyImportOpts) Ephemeral() bool {
	return opts.Temporary
}
// AESKeyGenOpts contains options for AES key generation at default security level
type AESKeyGenOpts struct {
	Temporary bool
}
// AES256ImportKeyOpts contains options for importing AES 256 keys.
type AES256ImportKeyOpts struct {
	Temporary bool
}
// AES Advanced Encryption Standard at the default security level.
// Each BCCSP may or may not support default security level. If not supported than
// an error will be returned.
const AES = "AES"
// Algorithm returns the key importation algorithm identifier (to be used).
func (opts *AES256ImportKeyOpts) Algorithm() string {
	return AES
}
// Ephemeral returns true if the key generated has to be ephemeral,
// false otherwise.
func (opts *AES256ImportKeyOpts) Ephemeral() bool {
	return opts.Temporary
}
// RSAKeyGenOpts contains options for RSA key generation.
type RSAKeyGenOpts struct {
	Temporary bool
}
// ECDSAGoPublicKeyImportOpts contains options for RSA key importation from rsa.PublicKey
type RSAGoPublicKeyImportOpts struct {
	Temporary bool
}
// RSA at the default security level.
// Each BCCSP may or may not support default security level. If not supported than
// an error will be returned.
const RSA = "RSA"
// Algorithm returns the key importation algorithm identifier (to be used).
func (opts *RSAGoPublicKeyImportOpts) Algorithm() string {
	return RSA
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *RSAGoPublicKeyImportOpts) Ephemeral() bool {
	return opts.Temporary
}
// HMACTruncated256AESDeriveKeyOpts contains options for HMAC truncated
// at 256 bits key derivation.
type HMACTruncated256AESDeriveKeyOpts struct {
	Temporary bool
	Arg       []byte
}
// HMACTruncated256 HMAC truncated at 256 bits.
const HMACTruncated256 = "HMAC_TRUNCATED_256"
// Algorithm returns the key derivation algorithm identifier (to be used).
func (opts *HMACTruncated256AESDeriveKeyOpts) Algorithm() string {
	return HMACTruncated256
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *HMACTruncated256AESDeriveKeyOpts) Ephemeral() bool {
	return opts.Temporary
}
// Argument returns the argument to be passed to the HMAC
func (opts *HMACTruncated256AESDeriveKeyOpts) Argument() []byte {
	return opts.Arg
}
// HMACImportKeyOpts contains options for importing HMAC keys.
type HMACImportKeyOpts struct {
	Temporary bool
}
// HMAC keyed-hash message authentication code
const HMAC = "HMAC"
// Algorithm returns the key importation algorithm identifier (to be used).
func (opts *HMACImportKeyOpts) Algorithm() string {
	return HMAC
}
// Ephemeral returns true if the key generated has to be ephemeral,
// false otherwise.
func (opts *HMACImportKeyOpts) Ephemeral() bool {
	return opts.Temporary
}
// HMACDeriveKeyOpts contains options for HMAC key derivation.
type HMACDeriveKeyOpts struct {
	Temporary bool
	Arg       []byte
}
// Algorithm returns the key derivation algorithm identifier (to be used).
func (opts *HMACDeriveKeyOpts) Algorithm() string {
	return HMAC
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *HMACDeriveKeyOpts) Ephemeral() bool {
	return opts.Temporary
}
// Argument returns the argument to be passed to the HMAC
func (opts *HMACDeriveKeyOpts) Argument() []byte {
	return opts.Arg
}
// X509PublicKeyImportOpts contains options for importing public keys from an x509 certificate
type X509PublicKeyImportOpts struct {
	Temporary bool
}
// X509Certificate Label for X509 certificate related operation
const X509Certificate = "X509Certificate"
// Algorithm returns the key importation algorithm identifier (to be used).
func (opts *X509PublicKeyImportOpts) Algorithm() string {
	return X509Certificate
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *X509PublicKeyImportOpts) Ephemeral() bool {
	return opts.Temporary
}

/*** hyperledger-mod/fabric/bccsp/hashopts.go ***/
// SHA256Opts contains options relating to SHA-256.
type SHA256Opts struct {}
// SHA384Opts contains options relating to SHA-384.
type SHA384Opts struct {}
// SHA3_256Opts contains options relating to SHA3-256.
type SHA3_256Opts struct {}
// SHA3_384Opts contains options relating to SHA3-384.
type SHA3_384Opts struct {}

/*** hyperledger/fabric/bccsp/ecdsaopts.go ***/
// ECDSAP256KeyGenOpts contains options for ECDSA key generation with curve P-256.
type ECDSAP256KeyGenOpts struct {
	Temporary bool
}
// ECDSA Elliptic Curve Digital Signature Algorithm over P-256 curve
const ECDSAP256 = "ECDSAP256"
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *ECDSAP256KeyGenOpts) Algorithm() string {
	return ECDSAP256
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *ECDSAP256KeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}
// ECDSAP384KeyGenOpts contains options for ECDSA key generation with curve P-384.
type ECDSAP384KeyGenOpts struct {
	Temporary bool
}
// ECDSA Elliptic Curve Digital Signature Algorithm over P-384 curve
const ECDSAP384 = "ECDSAP384"
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *ECDSAP384KeyGenOpts) Algorithm() string {
	return ECDSAP384
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *ECDSAP384KeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}

/*** hyperledger/fabric/bccsp/aesopts.go ***/
// AES128KeyGenOpts contains options for AES key generation at 128 security level
type AES128KeyGenOpts struct {
	Temporary bool
}
// AES192KeyGenOpts contains options for AES key generation at 192  security level
type AES192KeyGenOpts struct {
	Temporary bool
}
// AES256KeyGenOpts contains options for AES key generation at 256 security level
type AES256KeyGenOpts struct {
	Temporary bool
}

/*** hyperledger/fabric/bccsp/rsaopts.go ***/
// RSA1024KeyGenOpts contains options for RSA key generation at 1024 security.
type RSA1024KeyGenOpts struct {
	Temporary bool
}
// RSA2048KeyGenOpts contains options for RSA key generation at 2048 security.
type RSA2048KeyGenOpts struct {
	Temporary bool
}
// RSA3072KeyGenOpts contains options for RSA key generation at 3072 security.
type RSA3072KeyGenOpts struct {
	Temporary bool
}
// RSA4096KeyGenOpts contains options for RSA key generation at 4096 security.
type RSA4096KeyGenOpts struct {
	Temporary bool
}

/*** hyperledger-mod/fabric/bccsp/sw/aes.go ***/
// GetRandomBytes returns len random looking bytes
func GetRandomBytes(len int) ([]byte, error) {
	if len < 0 {
		return nil, errors.New("Len must be larger than 0")
	}

	buffer := make([]byte, len)

	n, err := rand.Read(buffer)
	if err != nil {
		return nil, err
	}
	if n != len {
		return nil, fmt.Errorf("Buffer not filled. Requested [%d], got [%d]", len, n)
	}

	return buffer, nil
}

/*** hyperledger-mod/fabric/bccsp/sw/keygen.go ***/
type ecdsaKeyGenerator struct {
	curve elliptic.Curve
}
func (kg *ecdsaKeyGenerator) KeyGen(opts KeyGenOpts) (k Key, err error) { //SOURCE:bccsp.KeyGenOpts //SOURCE:bccsp.Key
	privKey, err := ecdsa.GenerateKey(kg.curve, rand.Reader)
	if err != nil {
		return nil, fmt.Errorf("Failed generating ECDSA key for [%v]: [%s]", kg.curve, err)
	}

	return &ecdsaPrivateKey{privKey}, nil
}
type aesKeyGenerator struct {
	length int
}
func (kg *aesKeyGenerator) KeyGen(opts KeyGenOpts) (k Key, err error) { //SOURCE:bccsp.KeyGenOpts //SOURCE:bccsp.Key
	lowLevelKey, err := GetRandomBytes(int(kg.length))
	if err != nil {
		return nil, fmt.Errorf("Failed generating AES %d key [%s]", kg.length, err)
	}

	return &aesPrivateKey{lowLevelKey, false}, nil
}
type rsaKeyGenerator struct {
	length int
}
func (kg *rsaKeyGenerator) KeyGen(opts KeyGenOpts) (k Key, err error) { //SOURCE:bccsp.KeyGenOpts //SOURCE:bccsp.Key
	lowLevelKey, err := rsa.GenerateKey(rand.Reader, int(kg.length))

	if err != nil {
		return nil, fmt.Errorf("Failed generating RSA %d key [%s]", kg.length, err)
	}

	return &rsaPrivateKey{lowLevelKey}, nil
}

/*** hyperledger-mod/fabric/bccsp/sw/keyderiv.go ***/
type ecdsaPublicKeyKeyDeriver struct{}
func (kd *ecdsaPublicKeyKeyDeriver) KeyDeriv(k Key, opts KeyDerivOpts) (dk Key, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.KeyDerivOpts
	// Validate opts
	if opts == nil {
		return nil, errors.New("Invalid opts parameter. It must not be nil.")
	}

	ecdsaK := k.(*ecdsaPublicKey)

	switch opts.(type) {
	// Re-randomized an ECDSA private key
	case *ECDSAReRandKeyOpts: //SOURCE:bccsp.ECDSAReRandKeyOpts
		reRandOpts := opts.(*ECDSAReRandKeyOpts) //SOURCE:bccsp.ECDSAReRandKeyOpts
		tempSK := &ecdsa.PublicKey{
			Curve: ecdsaK.pubKey.Curve,
			X:     new(big.Int),
			Y:     new(big.Int),
		}

		var k = new(big.Int).SetBytes(reRandOpts.ExpansionValue())
		var one = new(big.Int).SetInt64(1)
		n := new(big.Int).Sub(ecdsaK.pubKey.Params().N, one)
		k.Mod(k, n)
		k.Add(k, one)

		// Compute temporary public key
		tempX, tempY := ecdsaK.pubKey.ScalarBaseMult(k.Bytes())
		tempSK.X, tempSK.Y = tempSK.Add(
			ecdsaK.pubKey.X, ecdsaK.pubKey.Y,
			tempX, tempY,
		)

		// Verify temporary public key is a valid point on the reference curve
		isOn := tempSK.Curve.IsOnCurve(tempSK.X, tempSK.Y)
		if !isOn {
			return nil, errors.New("Failed temporary public key IsOnCurve check.")
		}

		return &ecdsaPublicKey{tempSK}, nil
	default:
		return nil, fmt.Errorf("Unsupported 'KeyDerivOpts' provided [%v]", opts)
	}
}
type ecdsaPrivateKeyKeyDeriver struct{}
func (kd *ecdsaPrivateKeyKeyDeriver) KeyDeriv(k Key, opts KeyDerivOpts) (dk Key, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.KeyDerivOpts
	// Validate opts
	if opts == nil {
		return nil, errors.New("Invalid opts parameter. It must not be nil.")
	}

	ecdsaK := k.(*ecdsaPrivateKey)

	switch opts.(type) {
	// Re-randomized an ECDSA private key
	case *ECDSAReRandKeyOpts: //SOURCE:bccsp.ECDSAReRandKeyOpts
		reRandOpts := opts.(*ECDSAReRandKeyOpts) //SOURCE:bccsp.ECDSAReRandKeyOpts
		tempSK := &ecdsa.PrivateKey{
			PublicKey: ecdsa.PublicKey{
				Curve: ecdsaK.privKey.Curve,
				X:     new(big.Int),
				Y:     new(big.Int),
			},
			D: new(big.Int),
		}

		var k = new(big.Int).SetBytes(reRandOpts.ExpansionValue())
		var one = new(big.Int).SetInt64(1)
		n := new(big.Int).Sub(ecdsaK.privKey.Params().N, one)
		k.Mod(k, n)
		k.Add(k, one)

		tempSK.D.Add(ecdsaK.privKey.D, k)
		tempSK.D.Mod(tempSK.D, ecdsaK.privKey.PublicKey.Params().N)

		// Compute temporary public key
		tempX, tempY := ecdsaK.privKey.PublicKey.ScalarBaseMult(k.Bytes())
		tempSK.PublicKey.X, tempSK.PublicKey.Y =
			tempSK.PublicKey.Add(
				ecdsaK.privKey.PublicKey.X, ecdsaK.privKey.PublicKey.Y,
				tempX, tempY,
			)

		// Verify temporary public key is a valid point on the reference curve
		isOn := tempSK.Curve.IsOnCurve(tempSK.PublicKey.X, tempSK.PublicKey.Y)
		if !isOn {
			return nil, errors.New("Failed temporary public key IsOnCurve check.")
		}

		return &ecdsaPrivateKey{tempSK}, nil
	default:
		return nil, fmt.Errorf("Unsupported 'KeyDerivOpts' provided [%v]", opts)
	}
}
type aesPrivateKeyKeyDeriver struct {
	bccsp *impl
}
func (kd *aesPrivateKeyKeyDeriver) KeyDeriv(k Key, opts KeyDerivOpts) (dk Key, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.KeyDerivOpts
	// Validate opts
	if opts == nil {
		return nil, errors.New("Invalid opts parameter. It must not be nil.")
	}

	aesK := k.(*aesPrivateKey)

	switch opts.(type) {
	case *HMACTruncated256AESDeriveKeyOpts: //SOURCE:bccsp.HMACTruncated256AESDeriveKeyOpts
		hmacOpts := opts.(*HMACTruncated256AESDeriveKeyOpts) //SOURCE:bccsp.HMACTruncated256AESDeriveKeyOpts

		mac := hmac.New(kd.bccsp.conf.hashFunction, aesK.privKey)
		mac.Write(hmacOpts.Argument())
		return &aesPrivateKey{mac.Sum(nil)[:kd.bccsp.conf.aesBitLength], false}, nil

	case *HMACDeriveKeyOpts: //SOURCE:bccsp.HMACDeriveKeyOpts
		hmacOpts := opts.(*HMACDeriveKeyOpts) //SOURCE:bccsp.HMACDeriveKeyOpts

		mac := hmac.New(kd.bccsp.conf.hashFunction, aesK.privKey)
		mac.Write(hmacOpts.Argument())
		return &aesPrivateKey{mac.Sum(nil), true}, nil
	default:
		return nil, fmt.Errorf("Unsupported 'KeyDerivOpts' provided [%v]", opts)
	}
}

/*** hyperledger-mod/fabric/bccsp/utils/slice.go ***/
// Clone clones the passed slice
func Clone(src []byte) []byte {
	clone := make([]byte, len(src))
	copy(clone, src)

	return clone
}

/*** hyperledger-mod/fabric/bccsp/utils/keys.go ***/
// struct to hold info required for PKCS#8
type pkcs8Info struct {
	Version             int
	PrivateKeyAlgorithm []asn1.ObjectIdentifier
	PrivateKey          []byte
}
type ecPrivateKey struct {
	Version       int
	PrivateKey    []byte
	NamedCurveOID asn1.ObjectIdentifier `asn1:"optional,explicit,tag:0"`
	PublicKey     asn1.BitString        `asn1:"optional,explicit,tag:1"`
}
var (
	oidNamedCurveP224 = asn1.ObjectIdentifier{1, 3, 132, 0, 33}
	oidNamedCurveP256 = asn1.ObjectIdentifier{1, 2, 840, 10045, 3, 1, 7}
	oidNamedCurveP384 = asn1.ObjectIdentifier{1, 3, 132, 0, 34}
	oidNamedCurveP521 = asn1.ObjectIdentifier{1, 3, 132, 0, 35}
)
var oidPublicKeyECDSA = asn1.ObjectIdentifier{1, 2, 840, 10045, 2, 1}
func oidFromNamedCurve(curve elliptic.Curve) (asn1.ObjectIdentifier, bool) {
	switch curve {
	case elliptic.P224():
		return oidNamedCurveP224, true
	case elliptic.P256():
		return oidNamedCurveP256, true
	case elliptic.P384():
		return oidNamedCurveP384, true
	case elliptic.P521():
		return oidNamedCurveP521, true
	}
	return nil, false
}
// PrivateKeyToPEM converts the private key to PEM format.
// EC private keys are converted to PKCS#8 format.
// RSA private keys are converted to PKCS#1 format.
func PrivateKeyToPEM(privateKey interface{}, pwd []byte) ([]byte, error) {
	// Validate inputs
	if len(pwd) != 0 {
		return PrivateKeyToEncryptedPEM(privateKey, pwd)
	}
	if privateKey == nil {
		return nil, errors.New("Invalid key. It must be different from nil.")
	}

	switch k := privateKey.(type) {
	case *ecdsa.PrivateKey:
		if k == nil {
			return nil, errors.New("Invalid ecdsa private key. It must be different from nil.")
		}

		// get the oid for the curve
		oidNamedCurve, ok := oidFromNamedCurve(k.Curve)
		if !ok {
			return nil, errors.New("unknown elliptic curve")
		}

		// based on https://golang.org/src/crypto/x509/sec1.go
		privateKeyBytes := k.D.Bytes()
		paddedPrivateKey := make([]byte, (k.Curve.Params().N.BitLen()+7)/8)
		copy(paddedPrivateKey[len(paddedPrivateKey)-len(privateKeyBytes):], privateKeyBytes)
		// omit NamedCurveOID for compatibility as it's optional
		asn1Bytes, err := asn1.Marshal(ecPrivateKey{
			Version:    1,
			PrivateKey: paddedPrivateKey,
			PublicKey:  asn1.BitString{Bytes: elliptic.Marshal(k.Curve, k.X, k.Y)},
		})

		if err != nil {
			return nil, fmt.Errorf("error marshaling EC key to asn1 [%s]", err)
		}

		var pkcs8Key pkcs8Info
		pkcs8Key.Version = 0
		pkcs8Key.PrivateKeyAlgorithm = make([]asn1.ObjectIdentifier, 2)
		pkcs8Key.PrivateKeyAlgorithm[0] = oidPublicKeyECDSA
		pkcs8Key.PrivateKeyAlgorithm[1] = oidNamedCurve
		pkcs8Key.PrivateKey = asn1Bytes

		pkcs8Bytes, err := asn1.Marshal(pkcs8Key)
		if err != nil {
			return nil, fmt.Errorf("error marshaling EC key to asn1 [%s]", err)
		}
		return pem.EncodeToMemory(
			&pem.Block{
				Type:  "PRIVATE KEY",
				Bytes: pkcs8Bytes,
			},
		), nil
	case *rsa.PrivateKey:
		if k == nil {
			return nil, errors.New("Invalid rsa private key. It must be different from nil.")
		}
		raw := x509.MarshalPKCS1PrivateKey(k)

		return pem.EncodeToMemory(
			&pem.Block{
				Type:  "RSA PRIVATE KEY",
				Bytes: raw,
			},
		), nil
	default:
		return nil, errors.New("Invalid key type. It must be *ecdsa.PrivateKey or *rsa.PrivateKey")
	}
}
// PrivateKeyToEncryptedPEM converts a private key to an encrypted PEM
func PrivateKeyToEncryptedPEM(privateKey interface{}, pwd []byte) ([]byte, error) {
	if privateKey == nil {
		return nil, errors.New("Invalid private key. It must be different from nil.")
	}

	switch k := privateKey.(type) {
	case *ecdsa.PrivateKey:
		if k == nil {
			return nil, errors.New("Invalid ecdsa private key. It must be different from nil.")
		}
		raw, err := x509.MarshalECPrivateKey(k)

		if err != nil {
			return nil, err
		}

		block, err := x509.EncryptPEMBlock(
			rand.Reader,
			"PRIVATE KEY",
			raw,
			pwd,
			x509.PEMCipherAES256)

		if err != nil {
			return nil, err
		}

		return pem.EncodeToMemory(block), nil

	default:
		return nil, errors.New("Invalid key type. It must be *ecdsa.PrivateKey")
	}
}
// PEMtoPrivateKey unmarshals a pem to private key
func PEMtoPrivateKey(raw []byte, pwd []byte) (interface{}, error) {
	if len(raw) == 0 {
		return nil, errors.New("Invalid PEM. It must be different from nil.")
	}
	block, _ := pem.Decode(raw)
	if block == nil {
		return nil, fmt.Errorf("Failed decoding PEM. Block must be different from nil. [% x]", raw)
	}

	// TODO: derive from header the type of the key

	if x509.IsEncryptedPEMBlock(block) {
		if len(pwd) == 0 {
			return nil, errors.New("Encrypted Key. Need a password")
		}

		decrypted, err := x509.DecryptPEMBlock(block, pwd)
		if err != nil {
			return nil, fmt.Errorf("Failed PEM decryption [%s]", err)
		}

		key, err := DERToPrivateKey(decrypted)
		if err != nil {
			return nil, err
		}
		return key, err
	}

	cert, err := DERToPrivateKey(block.Bytes)
	if err != nil {
		return nil, err
	}
	return cert, err
}
// PEMtoPublicKey unmarshals a pem to public key
func PEMtoPublicKey(raw []byte, pwd []byte) (interface{}, error) {
	if len(raw) == 0 {
		return nil, errors.New("Invalid PEM. It must be different from nil.")
	}
	block, _ := pem.Decode(raw)
	if block == nil {
		return nil, fmt.Errorf("Failed decoding. Block must be different from nil. [% x]", raw)
	}

	// TODO: derive from header the type of the key
	if x509.IsEncryptedPEMBlock(block) {
		if len(pwd) == 0 {
			return nil, errors.New("Encrypted Key. Password must be different from nil")
		}

		decrypted, err := x509.DecryptPEMBlock(block, pwd)
		if err != nil {
			return nil, fmt.Errorf("Failed PEM decryption. [%s]", err)
		}

		key, err := DERToPublicKey(decrypted)
		if err != nil {
			return nil, err
		}
		return key, err
	}

	cert, err := DERToPublicKey(block.Bytes)
	if err != nil {
		return nil, err
	}
	return cert, err
}
// PublicKeyToPEM marshals a public key to the pem format
func PublicKeyToPEM(publicKey interface{}, pwd []byte) ([]byte, error) {
	if len(pwd) != 0 {
		return PublicKeyToEncryptedPEM(publicKey, pwd)
	}

	if publicKey == nil {
		return nil, errors.New("Invalid public key. It must be different from nil.")
	}

	switch k := publicKey.(type) {
	case *ecdsa.PublicKey:
		if k == nil {
			return nil, errors.New("Invalid ecdsa public key. It must be different from nil.")
		}
		PubASN1, err := x509.MarshalPKIXPublicKey(k)
		if err != nil {
			return nil, err
		}

		return pem.EncodeToMemory(
			&pem.Block{
				Type:  "PUBLIC KEY",
				Bytes: PubASN1,
			},
		), nil
	case *rsa.PublicKey:
		if k == nil {
			return nil, errors.New("Invalid rsa public key. It must be different from nil.")
		}
		PubASN1, err := x509.MarshalPKIXPublicKey(k)
		if err != nil {
			return nil, err
		}

		return pem.EncodeToMemory(
			&pem.Block{
				Type:  "RSA PUBLIC KEY",
				Bytes: PubASN1,
			},
		), nil

	default:
		return nil, errors.New("Invalid key type. It must be *ecdsa.PublicKey or *rsa.PublicKey")
	}
}
// PublicKeyToEncryptedPEM converts a public key to encrypted pem
func PublicKeyToEncryptedPEM(publicKey interface{}, pwd []byte) ([]byte, error) {
	if publicKey == nil {
		return nil, errors.New("Invalid public key. It must be different from nil.")
	}
	if len(pwd) == 0 {
		return nil, errors.New("Invalid password. It must be different from nil.")
	}

	switch k := publicKey.(type) {
	case *ecdsa.PublicKey:
		if k == nil {
			return nil, errors.New("Invalid ecdsa public key. It must be different from nil.")
		}
		raw, err := x509.MarshalPKIXPublicKey(k)
		if err != nil {
			return nil, err
		}

		block, err := x509.EncryptPEMBlock(
			rand.Reader,
			"PUBLIC KEY",
			raw,
			pwd,
			x509.PEMCipherAES256)

		if err != nil {
			return nil, err
		}

		return pem.EncodeToMemory(block), nil

	default:
		return nil, errors.New("Invalid key type. It must be *ecdsa.PublicKey")
	}
}
// DERToPrivateKey unmarshals a der to private key
func DERToPrivateKey(der []byte) (key interface{}, err error) {

	if key, err = x509.ParsePKCS1PrivateKey(der); err == nil {
		return key, nil
	}

	if key, err = x509.ParsePKCS8PrivateKey(der); err == nil {
		switch key.(type) {
		case *rsa.PrivateKey, *ecdsa.PrivateKey:
			return
		default:
			return nil, errors.New("Found unknown private key type in PKCS#8 wrapping")
		}
	}

	if key, err = x509.ParseECPrivateKey(der); err == nil {
		return
	}

	return nil, errors.New("Invalid key type. The DER must contain an rsa.PrivareKey or ecdsa.PrivateKey")
}
// DERToPublicKey unmarshals a der to public key
func DERToPublicKey(raw []byte) (pub interface{}, err error) {
	if len(raw) == 0 {
		return nil, errors.New("Invalid DER. It must be different from nil.")
	}

	key, err := x509.ParsePKIXPublicKey(raw)

	return key, err
}
// PEMtoAES extracts from the PEM an AES key
func PEMtoAES(raw []byte, pwd []byte) ([]byte, error) {
	if len(raw) == 0 {
		return nil, errors.New("Invalid PEM. It must be different from nil.")
	}
	block, _ := pem.Decode(raw)
	if block == nil {
		return nil, fmt.Errorf("Failed decoding PEM. Block must be different from nil. [% x]", raw)
	}

	if x509.IsEncryptedPEMBlock(block) {
		if len(pwd) == 0 {
			return nil, errors.New("Encrypted Key. Password must be different fom nil")
		}

		decrypted, err := x509.DecryptPEMBlock(block, pwd)
		if err != nil {
			return nil, fmt.Errorf("Failed PEM decryption. [%s]", err)
		}
		return decrypted, nil
	}

	return block.Bytes, nil
}
// AEStoPEM encapsulates an AES key in the PEM format
func AEStoPEM(raw []byte) []byte {
	return pem.EncodeToMemory(&pem.Block{Type: "AES PRIVATE KEY", Bytes: raw})
}
// AEStoEncryptedPEM encapsulates an AES key in the encrypted PEM format
func AEStoEncryptedPEM(raw []byte, pwd []byte) ([]byte, error) {
	if len(raw) == 0 {
		return nil, errors.New("Invalid aes key. It must be different from nil")
	}
	if len(pwd) == 0 {
		return AEStoPEM(raw), nil
	}

	block, err := x509.EncryptPEMBlock(
		rand.Reader,
		"AES PRIVATE KEY",
		raw,
		pwd,
		x509.PEMCipherAES256)

	if err != nil {
		return nil, err
	}

	return pem.EncodeToMemory(block), nil
}

/*** hyperledger-mod/fabric/bccsp/sw/keyimport.go ***/
type aes256ImportKeyOptsKeyImporter struct{}
func (*aes256ImportKeyOptsKeyImporter) KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error) { //SOURCE:bccsp.KeyImportOpts //SOURCE:bccsp.Key
	aesRaw, ok := raw.([]byte)
	if !ok {
		return nil, errors.New("Invalid raw material. Expected byte array.")
	}

	if aesRaw == nil {
		return nil, errors.New("Invalid raw material. It must not be nil.")
	}

	if len(aesRaw) != 32 {
		return nil, fmt.Errorf("Invalid Key Length [%d]. Must be 32 bytes", len(aesRaw))
	}

	return &aesPrivateKey{Clone(aesRaw), false}, nil //SOURCE:utils.Clone
}
type hmacImportKeyOptsKeyImporter struct{}
func (*hmacImportKeyOptsKeyImporter) KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error) { //SOURCE:bccsp.KeyImportOpts //SOURCE:bccsp.Key
	aesRaw, ok := raw.([]byte)
	if !ok {
		return nil, errors.New("Invalid raw material. Expected byte array.")
	}

	if len(aesRaw) == 0 {
		return nil, errors.New("Invalid raw material. It must not be nil.")
	}

	return &aesPrivateKey{Clone(aesRaw), false}, nil //SOURCE:utils.Clone
}
type ecdsaPKIXPublicKeyImportOptsKeyImporter struct{}
func (*ecdsaPKIXPublicKeyImportOptsKeyImporter) KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error) { //SOURCE:bccsp.KeyImportOpts //SOURCE:bccsp.Key
	der, ok := raw.([]byte)
	if !ok {
		return nil, errors.New("Invalid raw material. Expected byte array.")
	}

	if len(der) == 0 {
		return nil, errors.New("Invalid raw. It must not be nil.")
	}

	lowLevelKey, err := DERToPublicKey(der) //SOURCE:utils.DERToPublicKey
	if err != nil {
		return nil, fmt.Errorf("Failed converting PKIX to ECDSA public key [%s]", err)
	}

	ecdsaPK, ok := lowLevelKey.(*ecdsa.PublicKey)
	if !ok {
		return nil, errors.New("Failed casting to ECDSA public key. Invalid raw material.")
	}

	return &ecdsaPublicKey{ecdsaPK}, nil
}
type ecdsaPrivateKeyImportOptsKeyImporter struct{}
func (*ecdsaPrivateKeyImportOptsKeyImporter) KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error) { //SOURCE:bccsp.KeyImportOpts //SOURCE:bccsp.Key
	der, ok := raw.([]byte)
	if !ok {
		return nil, errors.New("[ECDSADERPrivateKeyImportOpts] Invalid raw material. Expected byte array.")
	}

	if len(der) == 0 {
		return nil, errors.New("[ECDSADERPrivateKeyImportOpts] Invalid raw. It must not be nil.")
	}

	lowLevelKey, err := DERToPrivateKey(der) //SOURCE:utils.DERToPrivateKey
	if err != nil {
		return nil, fmt.Errorf("Failed converting PKIX to ECDSA public key [%s]", err)
	}

	ecdsaSK, ok := lowLevelKey.(*ecdsa.PrivateKey)
	if !ok {
		return nil, errors.New("Failed casting to ECDSA private key. Invalid raw material.")
	}

	return &ecdsaPrivateKey{ecdsaSK}, nil
}
type ecdsaGoPublicKeyImportOptsKeyImporter struct{}
func (*ecdsaGoPublicKeyImportOptsKeyImporter) KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error) { //SOURCE:bccsp.KeyImportOpts //SOURCE:bccsp.Key
	lowLevelKey, ok := raw.(*ecdsa.PublicKey)
	if !ok {
		return nil, errors.New("Invalid raw material. Expected *ecdsa.PublicKey.")
	}

	return &ecdsaPublicKey{lowLevelKey}, nil
}
type rsaGoPublicKeyImportOptsKeyImporter struct{}
func (*rsaGoPublicKeyImportOptsKeyImporter) KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error) { //SOURCE:bccsp.KeyImportOpts //SOURCE:bccsp.Key
	lowLevelKey, ok := raw.(*rsa.PublicKey)
	if !ok {
		return nil, errors.New("Invalid raw material. Expected *rsa.PublicKey.")
	}

	return &rsaPublicKey{lowLevelKey}, nil
}
type x509PublicKeyImportOptsKeyImporter struct {
	bccsp *impl
}
func (ki *x509PublicKeyImportOptsKeyImporter) KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error) { //SOURCE:bccsp.KeyImportOpts //SOURCE:bccsp.Key
	x509Cert, ok := raw.(*x509.Certificate)
	if !ok {
		return nil, errors.New("Invalid raw material. Expected *x509.Certificate.")
	}

	pk := x509Cert.PublicKey

	switch pk.(type) {
	case *ecdsa.PublicKey:
		return ki.bccsp.keyImporters[reflect.TypeOf(&ECDSAGoPublicKeyImportOpts{})].KeyImport( //SOURCE:bccsp.ECDSAGoPublicKeyImportOpts
			pk,
			&ECDSAGoPublicKeyImportOpts{Temporary: opts.Ephemeral()}) //SOURCE:bccsp.ECDSAGoPublicKeyImportOpts
	case *rsa.PublicKey:
		return ki.bccsp.keyImporters[reflect.TypeOf(&RSAGoPublicKeyImportOpts{})].KeyImport( //SOURCE:bccsp.RSAGoPublicKeyImportOpts
			pk,
			&RSAGoPublicKeyImportOpts{Temporary: opts.Ephemeral()}) //SOURCE:bccsp.RSAGoPublicKeyImportOpts
	default:
		return nil, errors.New("Certificate's public key type not recognized. Supported keys: [ECDSA, RSA]")
	}
}

/*** hyperledger-mod/fabric/bccsp/sw/impl.go ***/
// SoftwareBasedBCCSP is the software-based implementation of the BCCSP.
type impl struct {
	conf *config
	ks   KeyStore //SOURCE:bccsp.KeyStore

	keyGenerators map[reflect.Type]KeyGenerator
	keyDerivers   map[reflect.Type]KeyDeriver
	keyImporters  map[reflect.Type]KeyImporter
	encryptors    map[reflect.Type]Encryptor
	decryptors    map[reflect.Type]Decryptor
	signers       map[reflect.Type]Signer
	verifiers     map[reflect.Type]Verifier
	hashers       map[reflect.Type]Hasher
}
// KeyGen generates a key using opts.
func (csp *impl) KeyGen(opts KeyGenOpts) (k Key, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.KeyGenOpts
	// Validate arguments
	if opts == nil {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid Opts parameter. It must not be nil.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}

	keyGenerator, found := csp.keyGenerators[reflect.TypeOf(opts)]
	if !found {
		return nil, ErrorWithCallstack(BCCSP_const, NotFound, "Unsupported 'KeyGenOpts' provided [%v]", opts) //SOURCE:errors.BCCSP //SOURCE:errors.NotFound //SOURCE:errors.ErrorWithCallstack
	}

	k, err = keyGenerator.KeyGen(opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed generating key with opts [%v]", opts).WrapError(err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
	}

	// If the key is not Ephemeral, store it.
	if !opts.Ephemeral() {
		// Store the key
		err = csp.ks.StoreKey(k)
		if err != nil {
			return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed storing key [%s]. [%s]", opts.Algorithm(), err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
		}
	}

	return k, nil
}
// KeyDeriv derives a key from k using opts.
// The opts argument should be appropriate for the primitive used.
func (csp *impl) KeyDeriv(k Key, opts KeyDerivOpts) (dk Key, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.KeyDerivOpts
	// Validate arguments
	if k == nil {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid Key. It must not be nil.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}
	if opts == nil {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid opts. It must not be nil.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}

	keyDeriver, found := csp.keyDerivers[reflect.TypeOf(k)]
	if !found {
		return nil, ErrorWithCallstack(BCCSP_const, NotFound, "Unsupported 'Key' provided [%v]", k) //SOURCE:errors.BCCSP //SOURCE:errors.NotFound //SOURCE:errors.ErrorWithCallstack
	}

	k, err = keyDeriver.KeyDeriv(k, opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed deriving key with opts [%v]", opts).WrapError(err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
	}

	// If the key is not Ephemeral, store it.
	if !opts.Ephemeral() {
		// Store the key
		err = csp.ks.StoreKey(k)
		if err != nil {
			return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed storing key [%s]. [%s]", opts.Algorithm(), err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
		}
	}

	return k, nil
}
// KeyImport imports a key from its raw representation using opts.
// The opts argument should be appropriate for the primitive used.
func (csp *impl) KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error) { //SOURCE:bccsp.KeyImportOpts //SOURCE:bccsp.Key
	// Validate arguments
	if raw == nil {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid raw. It must not be nil.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}
	if opts == nil {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid opts. It must not be nil.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}

	keyImporter, found := csp.keyImporters[reflect.TypeOf(opts)]
	if !found {
		return nil, ErrorWithCallstack(BCCSP_const, NotFound, "Unsupported 'KeyImportOpts' provided [%v]", opts) //SOURCE:errors.BCCSP //SOURCE:errors.NotFound //SOURCE:errors.ErrorWithCallstack
	}

	k, err = keyImporter.KeyImport(raw, opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed importing key with opts [%v]", opts).WrapError(err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
	}

	// If the key is not Ephemeral, store it.
	if !opts.Ephemeral() {
		// Store the key
		err = csp.ks.StoreKey(k)
		if err != nil {
			return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed storing imported key with opts [%v]", opts).WrapError(err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
		}
	}

	return
}
// GetKey returns the key this CSP associates to
// the Subject Key Identifier ski.
func (csp *impl) GetKey(ski []byte) (k Key, err error) { //SOURCE:bccsp.Key
	k, err = csp.ks.GetKey(ski)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed getting key for SKI [%v]", ski).WrapError(err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
	}

	return
}
// Hash hashes messages msg using options opts.
func (csp *impl) Hash(msg []byte, opts HashOpts) (digest []byte, err error) { //SOURCE:bccsp.HashOpts
	// Validate arguments
	if opts == nil {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid opts. It must not be nil.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}

	hasher, found := csp.hashers[reflect.TypeOf(opts)]
	if !found {
		return nil, ErrorWithCallstack(BCCSP_const, NotFound, "Unsupported 'HashOpt' provided [%v]", opts) //SOURCE:errors.BCCSP //SOURCE:errors.NotFound //SOURCE:errors.ErrorWithCallstack
	}

	digest, err = hasher.Hash(msg, opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed hashing with opts [%v]", opts).WrapError(err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
	}

	return
}
// GetHash returns and instance of hash.Hash using options opts.
// If opts is nil then the default hash function is returned.
func (csp *impl) GetHash(opts HashOpts) (h hash.Hash, err error) { //SOURCE:bccsp.HashOpts
	// Validate arguments
	if opts == nil {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid opts. It must not be nil.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}

	hasher, found := csp.hashers[reflect.TypeOf(opts)]
	if !found {
		return nil, ErrorWithCallstack(BCCSP_const, NotFound, "Unsupported 'HashOpt' provided [%v]", opts) //SOURCE:errors.BCCSP //SOURCE:errors.NotFound //SOURCE:errors.ErrorWithCallstack
	}

	h, err = hasher.GetHash(opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed getting hash function with opts [%v]", opts).WrapError(err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
	}

	return
}
// Sign signs digest using key k.
// The opts argument should be appropriate for the primitive used.
//
// Note that when a signature of a hash of a larger message is needed,
// the caller is responsible for hashing the larger message and passing
// the hash (as digest).
func (csp *impl) Sign(k Key, digest []byte, opts SignerOpts) (signature []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	// Validate arguments
	if k == nil {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid Key. It must not be nil.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}
	if len(digest) == 0 {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid digest. Cannot be empty.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}

	signer, found := csp.signers[reflect.TypeOf(k)]
	if !found {
		return nil, ErrorWithCallstack(BCCSP_const, NotFound, "Unsupported 'SignKey' provided [%v]", k) //SOURCE:errors.BCCSP //SOURCE:errors.NotFound //SOURCE:errors.ErrorWithCallstack
	}

	signature, err = signer.Sign(k, digest, opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed signing with opts [%v]", opts).WrapError(err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
	}

	return
}
// Verify verifies signature against key k and digest
func (csp *impl) Verify(k Key, signature, digest []byte, opts SignerOpts) (valid bool, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	// Validate arguments
	if k == nil {
		return false, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid Key. It must not be nil.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}
	if len(signature) == 0 {
		return false, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid signature. Cannot be empty.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}
	if len(digest) == 0 {
		return false, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid digest. Cannot be empty.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}

	verifier, found := csp.verifiers[reflect.TypeOf(k)]
	if !found {
		return false, ErrorWithCallstack(BCCSP_const, NotFound, "Unsupported 'VerifyKey' provided [%v]", k) //SOURCE:errors.BCCSP //SOURCE:errors.NotFound //SOURCE:errors.ErrorWithCallstack
	}

	valid, err = verifier.Verify(k, signature, digest, opts)
	if err != nil {
		return false, ErrorWithCallstack(BCCSP_const, Internal, "Failed verifing with opts [%v]", opts).WrapError(err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
	}

	return
}
// Encrypt encrypts plaintext using key k.
// The opts argument should be appropriate for the primitive used.
func (csp *impl) Encrypt(k Key, plaintext []byte, opts EncrypterOpts) (ciphertext []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.EncrypterOpts
	// Validate arguments
	if k == nil {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid Key. It must not be nil.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}

	encryptor, found := csp.encryptors[reflect.TypeOf(k)]
	if !found {
		return nil, ErrorWithCallstack(BCCSP_const, NotFound, "Unsupported 'EncryptKey' provided [%v]", k) //SOURCE:errors.BCCSP //SOURCE:errors.NotFound //SOURCE:errors.ErrorWithCallstack
	}

	return encryptor.Encrypt(k, plaintext, opts)
}
// Decrypt decrypts ciphertext using key k.
// The opts argument should be appropriate for the primitive used.
func (csp *impl) Decrypt(k Key, ciphertext []byte, opts DecrypterOpts) (plaintext []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.DecrypterOpts
	// Validate arguments
	if k == nil {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid Key. It must not be nil.") //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest //SOURCE:errors.ErrorWithCallstack
	}

	decryptor, found := csp.decryptors[reflect.TypeOf(k)]
	if !found {
		return nil, ErrorWithCallstack(BCCSP_const, NotFound, "Unsupported 'DecryptKey' provided [%v]", k) //SOURCE:errors.BCCSP //SOURCE:errors.NotFound //SOURCE:errors.ErrorWithCallstack
	}

	plaintext, err = decryptor.Decrypt(k, ciphertext, opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed decrypting with opts [%v]", opts).WrapError(err) //SOURCE:errors.BCCSP //SOURCE:errors.Internal //SOURCE:errors.ErrorWithCallstack
	}

	return
}
// New returns a new instance of the software-based BCCSP
// set at the passed security level, hash family and KeyStore.
func New(securityLevel int, hashFamily string, keyStore KeyStore) (BCCSP, error) { //SOURCE:bccsp.KeyStore //SOURCE:bccsp.BCCSP
	// Init config
	conf := &config{}
	err := conf.setSecurityLevel(securityLevel, hashFamily)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSP_const, Internal, "Failed initializing configuration at [%v,%v]", securityLevel, hashFamily).WrapError(err) //WAS "BCCSP" //SOURCE:errors.ErrorWithCallstack //SOURCE:errors.BCCSP //SOURCE:errors.Internal
	}

	// Check KeyStore
	if keyStore == nil {
		return nil, ErrorWithCallstack(BCCSP_const, BadRequest, "Invalid bccsp.KeyStore instance. It must be different from nil.") //WAS "BCCSP" //SOURCE:errors.ErrorWithCallstack //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}

	// Set the encryptors
	encryptors := make(map[reflect.Type]Encryptor)
	encryptors[reflect.TypeOf(&aesPrivateKey{})] = &aescbcpkcs7Encryptor{}

	// Set the decryptors
	decryptors := make(map[reflect.Type]Decryptor)
	decryptors[reflect.TypeOf(&aesPrivateKey{})] = &aescbcpkcs7Decryptor{}

	// Set the signers
	signers := make(map[reflect.Type]Signer)
	signers[reflect.TypeOf(&ecdsaPrivateKey{})] = &ecdsaSigner{}
	signers[reflect.TypeOf(&rsaPrivateKey{})] = &rsaSigner{}

	// Set the verifiers
	verifiers := make(map[reflect.Type]Verifier)
	verifiers[reflect.TypeOf(&ecdsaPrivateKey{})] = &ecdsaPrivateKeyVerifier{}
	verifiers[reflect.TypeOf(&ecdsaPublicKey{})] = &ecdsaPublicKeyKeyVerifier{}
	verifiers[reflect.TypeOf(&rsaPrivateKey{})] = &rsaPrivateKeyVerifier{}
	verifiers[reflect.TypeOf(&rsaPublicKey{})] = &rsaPublicKeyKeyVerifier{}

	// Set the hashers
	hashers := make(map[reflect.Type]Hasher)
	hashers[reflect.TypeOf(&SHAOpts{})] = &hasher{hash: conf.hashFunction} //SOURCE:bccsp.SHAOpts
	hashers[reflect.TypeOf(&SHA256Opts{})] = &hasher{hash: sha256.New} //SOURCE:bccsp.SHA256Opts
	hashers[reflect.TypeOf(&SHA384Opts{})] = &hasher{hash: sha512.New384} //SOURCE:bccsp.SHA384Opts
	hashers[reflect.TypeOf(&SHA3_256Opts{})] = &hasher{hash: sha3.New256} //SOURCE:bccsp.SHA3_256Opts
	hashers[reflect.TypeOf(&SHA3_384Opts{})] = &hasher{hash: sha3.New384} //SOURCE:bccsp.SHA3_384Opts

	impl := &impl{
		conf:       conf,
		ks:         keyStore,
		encryptors: encryptors,
		decryptors: decryptors,
		signers:    signers,
		verifiers:  verifiers,
		hashers:    hashers}

	// Set the key generators
	keyGenerators := make(map[reflect.Type]KeyGenerator)
	keyGenerators[reflect.TypeOf(&ECDSAKeyGenOpts{})] = &ecdsaKeyGenerator{curve: conf.ellipticCurve} //SOURCE:bccsp.ECDSAKeyGenOpts
	keyGenerators[reflect.TypeOf(&ECDSAP256KeyGenOpts{})] = &ecdsaKeyGenerator{curve: elliptic.P256()} //SOURCE:bccsp.ECDSAP256KeyGenOpts
	keyGenerators[reflect.TypeOf(&ECDSAP384KeyGenOpts{})] = &ecdsaKeyGenerator{curve: elliptic.P384()} //SOURCE:bccsp.ECDSAP384KeyGenOpts
	keyGenerators[reflect.TypeOf(&AESKeyGenOpts{})] = &aesKeyGenerator{length: conf.aesBitLength} //SOURCE:bccsp.AESKeyGenOpts
	keyGenerators[reflect.TypeOf(&AES256KeyGenOpts{})] = &aesKeyGenerator{length: 32} //SOURCE:bccsp.AES256KeyGenOpts
	keyGenerators[reflect.TypeOf(&AES192KeyGenOpts{})] = &aesKeyGenerator{length: 24} //SOURCE:bccsp.AES192KeyGenOpts
	keyGenerators[reflect.TypeOf(&AES128KeyGenOpts{})] = &aesKeyGenerator{length: 16} //SOURCE:bccsp.AES128KeyGenOpts
	keyGenerators[reflect.TypeOf(&RSAKeyGenOpts{})] = &rsaKeyGenerator{length: conf.rsaBitLength} //SOURCE:bccsp.RSAKeyGenOpts
	keyGenerators[reflect.TypeOf(&RSA1024KeyGenOpts{})] = &rsaKeyGenerator{length: 1024} //SOURCE:bccsp.RSA1024KeyGenOpts
	keyGenerators[reflect.TypeOf(&RSA2048KeyGenOpts{})] = &rsaKeyGenerator{length: 2048} //SOURCE:bccsp.RSA2048KeyGenOpts
	keyGenerators[reflect.TypeOf(&RSA3072KeyGenOpts{})] = &rsaKeyGenerator{length: 3072} //SOURCE:bccsp.RSA3072KeyGenOpts
	keyGenerators[reflect.TypeOf(&RSA4096KeyGenOpts{})] = &rsaKeyGenerator{length: 4096} //SOURCE:bccsp.RSA4096KeyGenOpts
	impl.keyGenerators = keyGenerators

	// Set the key generators
	keyDerivers := make(map[reflect.Type]KeyDeriver)
	keyDerivers[reflect.TypeOf(&ecdsaPrivateKey{})] = &ecdsaPrivateKeyKeyDeriver{}
	keyDerivers[reflect.TypeOf(&ecdsaPublicKey{})] = &ecdsaPublicKeyKeyDeriver{}
	keyDerivers[reflect.TypeOf(&aesPrivateKey{})] = &aesPrivateKeyKeyDeriver{bccsp: impl}
	impl.keyDerivers = keyDerivers

	// Set the key importers
	keyImporters := make(map[reflect.Type]KeyImporter)
	keyImporters[reflect.TypeOf(&AES256ImportKeyOpts{})] = &aes256ImportKeyOptsKeyImporter{} //SOURCE:bccsp.AES256ImportKeyOpts
	keyImporters[reflect.TypeOf(&HMACImportKeyOpts{})] = &hmacImportKeyOptsKeyImporter{} //SOURCE:bccsp.HMACImportKeyOpts
	keyImporters[reflect.TypeOf(&ECDSAPKIXPublicKeyImportOpts{})] = &ecdsaPKIXPublicKeyImportOptsKeyImporter{} //SOURCE:bccsp.ECDSAPKIXPublicKeyImportOpts
	keyImporters[reflect.TypeOf(&ECDSAPrivateKeyImportOpts{})] = &ecdsaPrivateKeyImportOptsKeyImporter{} //SOURCE:bccsp.ECDSAPrivateKeyImportOpts
	keyImporters[reflect.TypeOf(&ECDSAGoPublicKeyImportOpts{})] = &ecdsaGoPublicKeyImportOptsKeyImporter{} //SOURCE:bccsp.ECDSAGoPublicKeyImportOpts
	keyImporters[reflect.TypeOf(&RSAGoPublicKeyImportOpts{})] = &rsaGoPublicKeyImportOptsKeyImporter{} //SOURCE:bccsp.RSAGoPublicKeyImportOpts
	keyImporters[reflect.TypeOf(&X509PublicKeyImportOpts{})] = &x509PublicKeyImportOptsKeyImporter{bccsp: impl} //SOURCE:bccsp.X509PublicKeyImportOpts

	impl.keyImporters = keyImporters

	return impl, nil
}

/*** hyperledger/fabric/bccsp/utils/io.go ***/
// DirMissingOrEmpty checks is a directory is missin or empty
func DirMissingOrEmpty(path string) (bool, error) {
	dirExists, err := DirExists(path)
	if err != nil {
		return false, err
	}
	if !dirExists {
		return true, nil
	}

	dirEmpty, err := DirEmpty(path)
	if err != nil {
		return false, err
	}
	if dirEmpty {
		return true, nil
	}
	return false, nil
}
// DirExists checks if a directory exists
func DirExists(path string) (bool, error) {
	_, err := os.Stat(path)
	if err == nil {
		return true, nil
	}
	if os.IsNotExist(err) {
		return false, nil
	}
	return false, err
}
// DirEmpty checks if a directory is empty
func DirEmpty(path string) (bool, error) {
	f, err := os.Open(path)
	if err != nil {
		return false, err
	}
	defer f.Close()

	_, err = f.Readdir(1)
	if err == io.EOF {
		return true, nil
	}
	return false, err
}

/*** hyperledger/fabric/bccsp/utils/errs.go ***/
// ErrToString converts and error to a string. If the error is nil, it returns the string "<clean>"
func ErrToString(err error) string {
	if err != nil {
		return err.Error()
	}

	return "<clean>"
}

/*** hyperledger/fabric/bccsp/sw/fileks.go ***/
// NewFileBasedKeyStore instantiated a file-based key store at a given position.
// The key store can be encrypted if a non-empty password is specifiec.
// It can be also be set as read only. In this case, any store operation
// will be forbidden
func NewFileBasedKeyStore(pwd []byte, path string, readOnly bool) (KeyStore, error) { //SOURCE:bccsp.KeyStore
	ks := &fileBasedKeyStore{}
	return ks, ks.Init(pwd, path, readOnly)
}
// fileBasedKeyStore is a folder-based KeyStore.
// Each key is stored in a separated file whose name contains the key's SKI
// and flags to identity the key's type. All the keys are stored in
// a folder whose path is provided at initialization time.
// The KeyStore can be initialized with a password, this password
// is used to encrypt and decrypt the files storing the keys.
// A KeyStore can be read only to avoid the overwriting of keys.
type fileBasedKeyStore struct {
	path string

	readOnly bool
	isOpen   bool

	pwd []byte

	// Sync
	m sync.Mutex
}
// Init initializes this KeyStore with a password, a path to a folder
// where the keys are stored and a read only flag.
// Each key is stored in a separated file whose name contains the key's SKI
// and flags to identity the key's type.
// If the KeyStore is initialized with a password, this password
// is used to encrypt and decrypt the files storing the keys.
// The pwd can be nil for non-encrypted KeyStores. If an encrypted
// key-store is initialized without a password, then retrieving keys from the
// KeyStore will fail.
// A KeyStore can be read only to avoid the overwriting of keys.
func (ks *fileBasedKeyStore) Init(pwd []byte, path string, readOnly bool) error {
	// Validate inputs
	// pwd can be nil

	if len(path) == 0 {
		return errors.New("An invalid KeyStore path provided. Path cannot be an empty string.")
	}

	ks.m.Lock()
	defer ks.m.Unlock()

	if ks.isOpen {
		return errors.New("KeyStore already initilized.")
	}

	ks.path = path
	ks.pwd = Clone(pwd) //SOURCE:utils.Clone

	err := ks.createKeyStoreIfNotExists()
	if err != nil {
		return err
	}

	err = ks.openKeyStore()
	if err != nil {
		return err
	}

	ks.readOnly = readOnly

	return nil
}
// ReadOnly returns true if this KeyStore is read only, false otherwise.
// If ReadOnly is true then StoreKey will fail.
func (ks *fileBasedKeyStore) ReadOnly() bool {
	return ks.readOnly
}
// GetKey returns a key object whose SKI is the one passed.
func (ks *fileBasedKeyStore) GetKey(ski []byte) (k Key, err error) { //SOURCE:bccsp.Key
	// Validate arguments
	if len(ski) == 0 {
		return nil, errors.New("Invalid SKI. Cannot be of zero length.")
	}

	suffix := ks.getSuffix(hex.EncodeToString(ski))

	switch suffix {
	case "key":
		// Load the key
		key, err := ks.loadKey(hex.EncodeToString(ski))
		if err != nil {
			return nil, fmt.Errorf("Failed loading key [%x] [%s]", ski, err)
		}

		return &aesPrivateKey{key, false}, nil
	case "sk":
		// Load the private key
		key, err := ks.loadPrivateKey(hex.EncodeToString(ski))
		if err != nil {
			return nil, fmt.Errorf("Failed loading secret key [%x] [%s]", ski, err)
		}

		switch key.(type) {
		case *ecdsa.PrivateKey:
			return &ecdsaPrivateKey{key.(*ecdsa.PrivateKey)}, nil
		case *rsa.PrivateKey:
			return &rsaPrivateKey{key.(*rsa.PrivateKey)}, nil
		default:
			return nil, errors.New("Secret key type not recognized")
		}
	case "pk":
		// Load the public key
		key, err := ks.loadPublicKey(hex.EncodeToString(ski))
		if err != nil {
			return nil, fmt.Errorf("Failed loading public key [%x] [%s]", ski, err)
		}

		switch key.(type) {
		case *ecdsa.PublicKey:
			return &ecdsaPublicKey{key.(*ecdsa.PublicKey)}, nil
		case *rsa.PublicKey:
			return &rsaPublicKey{key.(*rsa.PublicKey)}, nil
		default:
			return nil, errors.New("Public key type not recognized")
		}
	default:
		return ks.searchKeystoreForSKI(ski)
	}
}
// StoreKey stores the key k in this KeyStore.
// If this KeyStore is read only then the method will fail.
func (ks *fileBasedKeyStore) StoreKey(k Key) (err error) { //SOURCE:bccsp.Key
	if ks.readOnly {
		return errors.New("Read only KeyStore.")
	}

	if k == nil {
		return errors.New("Invalid key. It must be different from nil.")
	}
	switch k.(type) {
	case *ecdsaPrivateKey:
		kk := k.(*ecdsaPrivateKey)

		err = ks.storePrivateKey(hex.EncodeToString(k.SKI()), kk.privKey)
		if err != nil {
			return fmt.Errorf("Failed storing ECDSA private key [%s]", err)
		}

	case *ecdsaPublicKey:
		kk := k.(*ecdsaPublicKey)

		err = ks.storePublicKey(hex.EncodeToString(k.SKI()), kk.pubKey)
		if err != nil {
			return fmt.Errorf("Failed storing ECDSA public key [%s]", err)
		}

	case *rsaPrivateKey:
		kk := k.(*rsaPrivateKey)

		err = ks.storePrivateKey(hex.EncodeToString(k.SKI()), kk.privKey)
		if err != nil {
			return fmt.Errorf("Failed storing RSA private key [%s]", err)
		}

	case *rsaPublicKey:
		kk := k.(*rsaPublicKey)

		err = ks.storePublicKey(hex.EncodeToString(k.SKI()), kk.pubKey)
		if err != nil {
			return fmt.Errorf("Failed storing RSA public key [%s]", err)
		}

	case *aesPrivateKey:
		kk := k.(*aesPrivateKey)

		err = ks.storeKey(hex.EncodeToString(k.SKI()), kk.privKey)
		if err != nil {
			return fmt.Errorf("Failed storing AES key [%s]", err)
		}

	default:
		return fmt.Errorf("Key type not reconigned [%s]", k)
	}

	return
}
func (ks *fileBasedKeyStore) searchKeystoreForSKI(ski []byte) (k Key, err error) { //SOURCE:bccsp.Key

	files, _ := ioutil.ReadDir(ks.path)
	for _, f := range files {
		if f.IsDir() {
			continue
		}
		raw, err := ioutil.ReadFile(filepath.Join(ks.path, f.Name()))
		if err != nil {
			continue
		}

		key, err := PEMtoPrivateKey(raw, ks.pwd) //SOURCE:utils.PEMtoPrivateKey
		if err != nil {
			continue
		}

		switch key.(type) {
		case *ecdsa.PrivateKey:
			k = &ecdsaPrivateKey{key.(*ecdsa.PrivateKey)}
		case *rsa.PrivateKey:
			k = &rsaPrivateKey{key.(*rsa.PrivateKey)}
		default:
			continue
		}

		if !bytes.Equal(k.SKI(), ski) {
			continue
		}

		return k, nil
	}
	return nil, errors.New("Key type not recognized")
}
func (ks *fileBasedKeyStore) getSuffix(alias string) string {
	files, _ := ioutil.ReadDir(ks.path)
	for _, f := range files {
		if strings.HasPrefix(f.Name(), alias) {
			if strings.HasSuffix(f.Name(), "sk") {
				return "sk"
			}
			if strings.HasSuffix(f.Name(), "pk") {
				return "pk"
			}
			if strings.HasSuffix(f.Name(), "key") {
				return "key"
			}
			break
		}
	}
	return ""
}
func (ks *fileBasedKeyStore) storePrivateKey(alias string, privateKey interface{}) error {
	rawKey, err := PrivateKeyToPEM(privateKey, ks.pwd) //SOURCE:utils.PrivateKeyToPEM
	if err != nil {
		logger.Errorf("Failed converting private key to PEM [%s]: [%s]", alias, err)
		return err
	}

	err = ioutil.WriteFile(ks.getPathForAlias(alias, "sk"), rawKey, 0700)
	if err != nil {
		logger.Errorf("Failed storing private key [%s]: [%s]", alias, err)
		return err
	}

	return nil
}
func (ks *fileBasedKeyStore) storePublicKey(alias string, publicKey interface{}) error {
	rawKey, err := PublicKeyToPEM(publicKey, ks.pwd) //SOURCE:utils.PublicKeyToPEM
	if err != nil {
		logger.Errorf("Failed converting public key to PEM [%s]: [%s]", alias, err)
		return err
	}

	err = ioutil.WriteFile(ks.getPathForAlias(alias, "pk"), rawKey, 0700)
	if err != nil {
		logger.Errorf("Failed storing private key [%s]: [%s]", alias, err)
		return err
	}

	return nil
}
func (ks *fileBasedKeyStore) storeKey(alias string, key []byte) error {
	pem, err := AEStoEncryptedPEM(key, ks.pwd) //SOURCE:utils.AEStoEncryptedPEM
	if err != nil {
		logger.Errorf("Failed converting key to PEM [%s]: [%s]", alias, err)
		return err
	}

	err = ioutil.WriteFile(ks.getPathForAlias(alias, "key"), pem, 0700)
	if err != nil {
		logger.Errorf("Failed storing key [%s]: [%s]", alias, err)
		return err
	}

	return nil
}
func (ks *fileBasedKeyStore) loadPrivateKey(alias string) (interface{}, error) {
	path := ks.getPathForAlias(alias, "sk")
	logger.Debugf("Loading private key [%s] at [%s]...", alias, path)

	raw, err := ioutil.ReadFile(path)
	if err != nil {
		logger.Errorf("Failed loading private key [%s]: [%s].", alias, err.Error())

		return nil, err
	}

	privateKey, err := PEMtoPrivateKey(raw, ks.pwd) //SOURCE:utils.PEMtoPrivateKey
	if err != nil {
		logger.Errorf("Failed parsing private key [%s]: [%s].", alias, err.Error())

		return nil, err
	}

	return privateKey, nil
}
func (ks *fileBasedKeyStore) loadPublicKey(alias string) (interface{}, error) {
	path := ks.getPathForAlias(alias, "pk")
	logger.Debugf("Loading public key [%s] at [%s]...", alias, path)

	raw, err := ioutil.ReadFile(path)
	if err != nil {
		logger.Errorf("Failed loading public key [%s]: [%s].", alias, err.Error())

		return nil, err
	}

	privateKey, err := PEMtoPublicKey(raw, ks.pwd) //SOURCE:utils.PEMtoPublicKey
	if err != nil {
		logger.Errorf("Failed parsing private key [%s]: [%s].", alias, err.Error())

		return nil, err
	}

	return privateKey, nil
}
func (ks *fileBasedKeyStore) loadKey(alias string) ([]byte, error) {
	path := ks.getPathForAlias(alias, "key")
	logger.Debugf("Loading key [%s] at [%s]...", alias, path)

	pem, err := ioutil.ReadFile(path)
	if err != nil {
		logger.Errorf("Failed loading key [%s]: [%s].", alias, err.Error())

		return nil, err
	}

	key, err := PEMtoAES(pem, ks.pwd) //SOURCE:utils.PEMtoAES
	if err != nil {
		logger.Errorf("Failed parsing key [%s]: [%s]", alias, err)

		return nil, err
	}

	return key, nil
}
func (ks *fileBasedKeyStore) createKeyStoreIfNotExists() error {
	// Check keystore directory
	ksPath := ks.path
	missing, err := DirMissingOrEmpty(ksPath) //SOURCE:utils.DirMissingOrEmpty

	if missing {
		logger.Debugf("KeyStore path [%s] missing [%t]: [%s]", ksPath, missing, ErrToString(err)) //SOURCE:utils.ErrToString

		err := ks.createKeyStore()
		if err != nil {
			logger.Errorf("Failed creating KeyStore At [%s]: [%s]", ksPath, err.Error())
			return nil
		}
	}

	return nil
}
func (ks *fileBasedKeyStore) createKeyStore() error {
	// Create keystore directory root if it doesn't exist yet
	ksPath := ks.path
	logger.Debugf("Creating KeyStore at [%s]...", ksPath)

	os.MkdirAll(ksPath, 0755)

	logger.Debugf("KeyStore created at [%s].", ksPath)
	return nil
}
func (ks *fileBasedKeyStore) openKeyStore() error {
	if ks.isOpen {
		return nil
	}

	logger.Debugf("KeyStore opened at [%s]...done", ks.path)

	return nil
}
func (ks *fileBasedKeyStore) getPathForAlias(alias, suffix string) string {
	return filepath.Join(ks.path, alias+"_"+suffix)
}

/*** hyperledger-mod/fabric/bccsp/sw/dummyks.go ***/
// NewDummyKeyStore instantiate a dummy key store
// that neither loads nor stores keys
func NewDummyKeyStore() KeyStore { //SOURCE:bccsp.KeyStore
	return &dummyKeyStore{}
}
// dummyKeyStore is a read-only KeyStore that neither loads nor stores keys.
type dummyKeyStore struct {}
// ReadOnly returns true if this KeyStore is read only, false otherwise.
// If ReadOnly is true then StoreKey will fail.
func (ks *dummyKeyStore) ReadOnly() bool {
	return true
}
// GetKey returns a key object whose SKI is the one passed.
func (ks *dummyKeyStore) GetKey(ski []byte) (k Key, err error) { //SOURCE:bccsp.Key
	return nil, errors.New("Key not found. This is a dummy KeyStore")
}
// StoreKey stores the key k in this KeyStore.
// If this KeyStore is read only then the method will fail.
func (ks *dummyKeyStore) StoreKey(k Key) (err error) { //SOURCE:bccsp.Key
	return errors.New("Cannot store key. This is a dummy read-only KeyStore")
}

/*** hyperledger/fabric/bccsp/keystore.go ***/
// KeyStore represents a storage system for cryptographic keys.
// It allows to store and retrieve bccsp.Key objects.
// The KeyStore can be read only, in that case StoreKey will return
// an error.
type KeyStore interface {

	// ReadOnly returns true if this KeyStore is read only, false otherwise.
	// If ReadOnly is true then StoreKey will fail.
	ReadOnly() bool

	// GetKey returns a key object whose SKI is the one passed.
	GetKey(ski []byte) (k Key, err error)

	// StoreKey stores the key k in this KeyStore.
	// If this KeyStore is read only then the method will fail.
	StoreKey(k Key) (err error)
}

/*** hyperledger/fabric/bccsp/bccsp.go ***/
// KeyGenOpts contains options for key-generation with a CSP.
type KeyGenOpts interface {

	// Algorithm returns the key generation algorithm identifier (to be used).
	Algorithm() string

	// Ephemeral returns true if the key to generate has to be ephemeral,
	// false otherwise.
	Ephemeral() bool
}
/*** hyperledger/fabric/bccsp/bccsp.go ***/
// KeyDerivOpts contains options for key-derivation with a CSP.
type KeyDerivOpts interface {

	// Algorithm returns the key derivation algorithm identifier (to be used).
	Algorithm() string

	// Ephemeral returns true if the key to derived has to be ephemeral,
	// false otherwise.
	Ephemeral() bool
}
/*** hyperledger/fabric/bccsp/bccsp.go ***/
// KeyImportOpts contains options for importing the raw material of a key with a CSP.
type KeyImportOpts interface {

	// Algorithm returns the key importation algorithm identifier (to be used).
	Algorithm() string

	// Ephemeral returns true if the key generated has to be ephemeral,
	// false otherwise.
	Ephemeral() bool
}
/*** hyperledger/fabric/bccsp/bccsp.go ***/
// HashOpts contains options for hashing with a CSP.
type HashOpts interface {

	// Algorithm returns the hash algorithm identifier (to be used).
	Algorithm() string
}
/*** hyperledger/fabric/bccsp/bccsp.go ***/
// SignerOpts contains options for signing with a CSP.
type SignerOpts interface {
	crypto.SignerOpts
}
/*** hyperledger/fabric/bccsp/bccsp.go ***/
// EncrypterOpts contains options for encrypting with a CSP.
type EncrypterOpts interface{}
/*** hyperledger/fabric/bccsp/bccsp.go ***/
// DecrypterOpts contains options for decrypting with a CSP.
type DecrypterOpts interface{}

/*** hyperledger/fabric/bccsp/pkcs11/pkcs11.go ***/
func loadLib(lib, pin, label string) (*pkcs11.Ctx, uint, *pkcs11.SessionHandle, error) {
	var slot uint = 0
	logger.Debugf("Loading pkcs11 library [%s]\n", lib)
	if lib == "" {
		return nil, slot, nil, fmt.Errorf("No PKCS11 library default")
	}

	ctx := pkcs11.New(lib)
	if ctx == nil {
		return nil, slot, nil, fmt.Errorf("Instantiate failed [%s]", lib)
	}

	ctx.Initialize()
	slots, err := ctx.GetSlotList(true)
	if err != nil {
		return nil, slot, nil, fmt.Errorf("Could not get Slot List [%s]", err)
	}
	found := false
	for _, s := range slots {
		info, err := ctx.GetTokenInfo(s)
		if err != nil {
			continue
		}
		logger.Debugf("Looking for %s, found label %s\n", label, info.Label)
		if label == info.Label {
			found = true
			slot = s
			break
		}
	}
	if !found {
		return nil, slot, nil, fmt.Errorf("Could not find token with label %s", label)
	}

	var session pkcs11.SessionHandle
	for i := 0; i < 10; i++ {
		session, err = ctx.OpenSession(slot, pkcs11.CKF_SERIAL_SESSION|pkcs11.CKF_RW_SESSION)
		if err != nil {
			logger.Warningf("OpenSession failed, retrying [%s]\n", err)
		} else {
			break
		}
	}
	if err != nil {
		logger.Fatalf("OpenSession [%s]\n", err)
	}
	logger.Debugf("Created new pkcs11 session %+v on slot %d\n", session, slot)

	if pin == "" {
		return nil, slot, nil, fmt.Errorf("No PIN set\n")
	}
	err = ctx.Login(session, pkcs11.CKU_USER, pin)
	if err != nil {
		if err != pkcs11.Error(pkcs11.CKR_USER_ALREADY_LOGGED_IN) {
			return nil, slot, nil, fmt.Errorf("Login failed [%s]\n", err)
		}
	}

	return ctx, slot, &session, nil
}
func (csp *implPkcs11) returnSession(session pkcs11.SessionHandle) {
	select {
	case csp.sessions <- session:
		// returned session back to session cache
	default:
		// have plenty of sessions in cache, dropping
		csp.ctx.CloseSession(session)
	}
}

/*** hyperledger/fabric/bccsp/pkcs11/impl.go ***/
var (
	sessionCacheSize = 10
)
// New returns a new instance of the software-based BCCSP
// set at the passed security level, hash family and KeyStore.
func NewPkcs11(opts PKCS11Opts, keyStore KeyStore) (BCCSP, error) { //SOURCE:bccsp.KeyStore //SOURCE:bccsp.BCCSP
	// Init config
	conf := &config{}
	err := conf.setSecurityLevel(opts.SecLevel, opts.HashFamily)
	if err != nil {
		return nil, fmt.Errorf("Failed initializing configuration [%s]", err)
	}

	swCSP, err := New(opts.SecLevel, opts.HashFamily, keyStore) //SOURCE:sw.New
	if err != nil {
		return nil, fmt.Errorf("Failed initializing fallback SW BCCSP [%s]", err)
	}

	// Check KeyStore
	if keyStore == nil {
		return nil, errors.New("Invalid bccsp.KeyStore instance. It must be different from nil.")
	}

	lib := opts.Library
	pin := opts.Pin
	label := opts.Label
	ctx, slot, session, err := loadLib(lib, pin, label)
	if err != nil {
		return nil, fmt.Errorf("Failed initializing PKCS11 library %s %s [%s]",
			lib, label, err)
	}

	sessions := make(chan pkcs11.SessionHandle, sessionCacheSize)
	csp := &implPkcs11{swCSP, conf, keyStore, ctx, sessions, slot, lib, opts.Sensitive, opts.SoftVerify}
	csp.returnSession(*session)
	return csp, nil
}
type implPkcs11 struct {
	BCCSP //SOURCE:bccsp.BCCSP

	conf *config
	ks   KeyStore //SOURCE:bccsp.KeyStore

	ctx      *pkcs11.Ctx
	sessions chan pkcs11.SessionHandle
	slot     uint

	lib          string
	noPrivImport bool
	softVerify   bool
}

/*** hyperledger-mod/fabric/bccsp/factory/pkcs11factory.go ***/
// PKCS11BasedFactoryName is the name of the factory of the hsm-based BCCSP implementation
const PKCS11BasedFactoryName = "PKCS11"
// PKCS11Factory is the factory of the HSM-based BCCSP.
type PKCS11Factory struct{}
// Name returns the name of this factory
func (f *PKCS11Factory) Name() string {
	return PKCS11BasedFactoryName
}
// Get returns an instance of BCCSP using Opts.
func (f *PKCS11Factory) Get(config *FactoryOpts) (BCCSP, error) { //SOURCE:bccsp.BCCSP
	// Validate arguments
	if config == nil || config.Pkcs11Opts == nil {
		return nil, errors.New("Invalid config. It must not be nil.")
	}

	p11Opts := config.Pkcs11Opts

	//TODO: PKCS11 does not need a keystore, but we have not migrated all of PKCS11 BCCSP to PKCS11 yet
	var ks KeyStore //SOURCE:bccsp.KeyStore
	if p11Opts.Ephemeral == true {
		ks = NewDummyKeyStore() //SOURCE:sw.NewDummyKeyStore
	} else if p11Opts.FileKeystore != nil {
		fks, err := NewFileBasedKeyStore(nil, p11Opts.FileKeystore.KeyStorePath, false) //SOURCE:sw.NewFileBasedKeyStore
		if err != nil {
			return nil, fmt.Errorf("Failed to initialize software key store: %s", err)
		}
		ks = fks
	} else {
		// Default to DummyKeystore
		ks = NewDummyKeyStore() //SOURCE:sw.NewDummyKeyStore
	}
	return NewPkcs11(*p11Opts, ks) //SOURCE:pkcs11.New
}

/*** hyperledger-mod/fabric/bccsp/factory/swfactory.go ***/
// SoftwareBasedFactoryName is the name of the factory of the software-based BCCSP implementation
const SoftwareBasedFactoryName = "SW"
// SWFactory is the factory of the software-based BCCSP.
type SWFactory struct{}
// Name returns the name of this factory
func (f *SWFactory) Name() string {
	return SoftwareBasedFactoryName
}
// Get returns an instance of BCCSP using Opts.
func (f *SWFactory) Get(config *FactoryOpts) (BCCSP, error) { //SOURCE:bccsp.BCCSP
	// Validate arguments
	if config == nil || config.SwOpts == nil {
		return nil, errors.New("Invalid config. It must not be nil.")
	}

	swOpts := config.SwOpts

	var ks KeyStore //SOURCE:bccsp.KeyStore
	if swOpts.Ephemeral == true {
		ks = NewDummyKeyStore() //SOURCE:sw.NewDummyKeyStore
	} else if swOpts.FileKeystore != nil {
		fks, err := NewFileBasedKeyStore(nil, swOpts.FileKeystore.KeyStorePath, false) //SOURCE:sw.NewFileBasedKeyStore
		if err != nil {
			return nil, fmt.Errorf("Failed to initialize software key store: %s", err)
		}
		ks = fks
	} else {
		// Default to DummyKeystore
		ks = NewDummyKeyStore() //SOURCE:sw.NewDummyKeyStore
	}

	return New(swOpts.SecLevel, swOpts.HashFamily, ks) //SOURCE:sw.New
}

/*** hyperledger/fabric/bccsp/factory/opts.go ***/
// GetDefaultOpts offers a default implementation for Opts
// returns a new instance every time
func GetDefaultOpts() *FactoryOpts {
	return &FactoryOpts{
		ProviderName: "SW",
		SwOpts: &SwOpts{
			HashFamily: "SHA2",
			SecLevel:   256,

			Ephemeral: true,
		},
	}
}

/*** hyperledger-mod/fabric/bccsp/factory/factory.go ***/
var (
	// Default BCCSP
	defaultBCCSP BCCSP //SOURCE:bccsp.BCCSP

	// when InitFactories has not been called yet (should only happen
	// in test cases), use this BCCSP temporarily
	bootBCCSP BCCSP //SOURCE:bccsp.BCCSP

	// BCCSP Factories
	bccspMap map[string]BCCSP //SOURCE:bccsp.BCCSP

	// factories' Sync on Initialization
	factoriesInitOnce sync.Once
	bootBCCSPInitOnce sync.Once

	// Factories' Initialization Error
	factoriesInitError error
)
// BCCSPFactory is used to get instances of the BCCSP interface.
// A Factory has name used to address it.
type BCCSPFactory interface {

	// Name returns the name of this factory
	Name() string

	// Get returns an instance of BCCSP using opts.
	Get(opts *FactoryOpts) (BCCSP, error) //SOURCE:bccsp.BCCSP
}
// GetDefault returns a non-ephemeral (long-term) BCCSP
func GetDefault() BCCSP { //SOURCE:bccsp.BCCSP
	if defaultBCCSP == nil {
		logger.Warning("Before using BCCSP, please call InitFactories(). Falling back to bootBCCSP.")
		bootBCCSPInitOnce.Do(func() {
			var err error
			f := &SWFactory{}
			bootBCCSP, err = f.Get(GetDefaultOpts())
			if err != nil {
				panic("BCCSP Internal error, failed initialization with GetDefaultOpts!")
			}
		})
		return bootBCCSP
	}
	return defaultBCCSP
}
func initBCCSP(f BCCSPFactory, config *FactoryOpts) error {
	csp, err := f.Get(config)
	if err != nil {
		return fmt.Errorf("Could not initialize BCCSP %s [%s]", f.Name(), err)
	}

	logger.Debugf("Initialize BCCSP [%s]", f.Name())
	bccspMap[f.Name()] = csp
	return nil
}

/*** hyperledger/fabric/bccsp/bccsp.go ***/
// BCCSP is the blockchain cryptographic service provider that offers
// the implementation of cryptographic standards and algorithms.
type BCCSP interface {

	// KeyGen generates a key using opts.
	KeyGen(opts KeyGenOpts) (k Key, err error)

	// KeyDeriv derives a key from k using opts.
	// The opts argument should be appropriate for the primitive used.
	KeyDeriv(k Key, opts KeyDerivOpts) (dk Key, err error)

	// KeyImport imports a key from its raw representation using opts.
	// The opts argument should be appropriate for the primitive used.
	KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error)

	// GetKey returns the key this CSP associates to
	// the Subject Key Identifier ski.
	GetKey(ski []byte) (k Key, err error)

	// Hash hashes messages msg using options opts.
	// If opts is nil, the default hash function will be used.
	Hash(msg []byte, opts HashOpts) (hash []byte, err error)

	// GetHash returns and instance of hash.Hash using options opts.
	// If opts is nil, the default hash function will be returned.
	GetHash(opts HashOpts) (h hash.Hash, err error)

	// Sign signs digest using key k.
	// The opts argument should be appropriate for the algorithm used.
	//
	// Note that when a signature of a hash of a larger message is needed,
	// the caller is responsible for hashing the larger message and passing
	// the hash (as digest).
	Sign(k Key, digest []byte, opts SignerOpts) (signature []byte, err error)

	// Verify verifies signature against key k and digest
	// The opts argument should be appropriate for the algorithm used.
	Verify(k Key, signature, digest []byte, opts SignerOpts) (valid bool, err error)

	// Encrypt encrypts plaintext using key k.
	// The opts argument should be appropriate for the algorithm used.
	Encrypt(k Key, plaintext []byte, opts EncrypterOpts) (ciphertext []byte, err error)

	// Decrypt decrypts ciphertext using key k.
	// The opts argument should be appropriate for the algorithm used.
	Decrypt(k Key, ciphertext []byte, opts DecrypterOpts) (plaintext []byte, err error)
}

/*** hyperledger/fabric/bccsp/factory/pkcs11.go ***/
// GetBCCSPFromOpts returns a BCCSP created according to the options passed in input.
func GetBCCSPFromOpts(config *FactoryOpts) (BCCSP, error) { //SOURCE:bccsp.BCCSP
	var f BCCSPFactory
	switch config.ProviderName {
	case "SW":
		f = &SWFactory{}
	case "PKCS11":
		f = &PKCS11Factory{}
	default:
		return nil, fmt.Errorf("Could not find BCCSP, no '%s' provider", config.ProviderName)
	}

	csp, err := f.Get(config)
	if err != nil {
		return nil, fmt.Errorf("Could not initialize BCCSP %s [%s]", f.Name(), err)
	}
	return csp, nil
}

/*** hyperledger/fabric/bccsp/factory/swfactory.go ***/
// Pluggable Keystores, could add JKS, P12, etc..
type FileKeystoreOpts struct {
	KeyStorePath string `mapstructure:"keystore" yaml:"KeyStore"`
}
/*** hyperledger/fabric/bccsp/factory/swfactory.go ***/
type DummyKeystoreOpts struct{}

/*** hyperledger/fabric/bccsp/factory/swfactory.go ***/
// SwOpts contains options for the SWFactory
type SwOpts struct {
	// Default algorithms when not specified (Deprecated?)
	SecLevel   int    `mapstructure:"security" json:"security" yaml:"Security"`
	HashFamily string `mapstructure:"hash" json:"hash" yaml:"Hash"`

	// Keystore Options
	Ephemeral     bool               `mapstructure:"tempkeys,omitempty" json:"tempkeys,omitempty"`
	FileKeystore  *FileKeystoreOpts  `mapstructure:"filekeystore,omitempty" json:"filekeystore,omitempty" yaml:"FileKeyStore"`
	DummyKeystore *DummyKeystoreOpts `mapstructure:"dummykeystore,omitempty" json:"dummykeystore,omitempty"`
}

/*** hyperledger/fabric/bccsp/pkcs11/conf.go ***/
// PKCS11Opts contains options for the P11Factory
type PKCS11Opts struct {
	// Default algorithms when not specified (Deprecated?)
	SecLevel   int    `mapstructure:"security" json:"security"`
	HashFamily string `mapstructure:"hash" json:"hash"`

	// Keystore options
	Ephemeral     bool               `mapstructure:"tempkeys,omitempty" json:"tempkeys,omitempty"`
	FileKeystore  *FileKeystoreOpts  `mapstructure:"filekeystore,omitempty" json:"filekeystore,omitempty"`
	DummyKeystore *DummyKeystoreOpts `mapstructure:"dummykeystore,omitempty" json:"dummykeystore,omitempty"`

	// PKCS11 options
	Library    string `mapstructure:"library" json:"library"`
	Label      string `mapstructure:"label" json:"label"`
	Pin        string `mapstructure:"pin" json:"pin"`
	Sensitive  bool   `mapstructure:"sensitivekeys,omitempty" json:"sensitivekeys,omitempty"`
	SoftVerify bool   `mapstructure:"softwareverify,omitempty" json:"softwareverify,omitempty"`
}

/*** hyperledger/fabric/bccsp/factory/pkcs11.go ***/
type FactoryOpts struct {
	ProviderName string             `mapstructure:"default" json:"default" yaml:"Default"`
	SwOpts       *SwOpts            `mapstructure:"SW,omitempty" json:"SW,omitempty" yaml:"SwOpts"`
	Pkcs11Opts   *PKCS11Opts `mapstructure:"PKCS11,omitempty" json:"PKCS11,omitempty" yaml:"PKCS11"` //SOURCE:pkcs11.PKCS11Opts
}
// InitFactories must be called before using factory interfaces
// It is acceptable to call with config = nil, in which case
// some defaults will get used
// Error is returned only if defaultBCCSP cannot be found
func InitFactories(config *FactoryOpts) error {
	factoriesInitOnce.Do(func() {
		setFactories(config)
	})

	return factoriesInitError
}
func setFactories(config *FactoryOpts) error {
	// Take some precautions on default opts
	if config == nil {
		config = GetDefaultOpts()
	}

	if config.ProviderName == "" {
		config.ProviderName = "SW"
	}

	if config.SwOpts == nil {
		config.SwOpts = GetDefaultOpts().SwOpts
	}

	// Initialize factories map
	bccspMap = make(map[string]BCCSP) //SOURCE:bccsp.BCCSP

	// Software-Based BCCSP
	if config.SwOpts != nil {
		f := &SWFactory{}
		err := initBCCSP(f, config)
		if err != nil {
			factoriesInitError = fmt.Errorf("Failed initializing SW.BCCSP [%s]", err)
		}
	}

	// PKCS11-Based BCCSP
	if config.Pkcs11Opts != nil {
		f := &PKCS11Factory{}
		err := initBCCSP(f, config)
		if err != nil {
			factoriesInitError = fmt.Errorf("Failed initializing PKCS11.BCCSP %s\n[%s]", factoriesInitError, err)
		}
	}

	var ok bool
	defaultBCCSP, ok = bccspMap[config.ProviderName]
	if !ok {
		factoriesInitError = fmt.Errorf("%s\nCould not find default `%s` BCCSP", factoriesInitError, config.ProviderName)
	}

	return factoriesInitError
}

/*** hyperledger/fabric/bccsp/bccsp.go ***/
// Key represents a cryptographic key
type Key interface {

	// Bytes converts this key to its byte representation,
	// if this operation is allowed.
	Bytes() ([]byte, error)

	// SKI returns the subject key identifier of this key.
	SKI() []byte

	// Symmetric returns true if this key is a symmetric key,
	// false is this key is asymmetric
	Symmetric() bool

	// Private returns true if this key is a private key,
	// false otherwise.
	Private() bool

	// PublicKey returns the corresponding public key part of an asymmetric public/private key pair.
	// This method returns an error in symmetric key schemes.
	PublicKey() (Key, error)
}

/*** hyperledger/fabric/bccsp/signer/signer.go ***/
// bccspCryptoSigner is the BCCSP-based implementation of a crypto.Signer
type bccspCryptoSigner struct {
	csp BCCSP //SOURCE:bccsp.BCCSP
	key Key //SOURCE:bccsp.Key
	pk  interface{}
}
// New returns a new BCCSP-based crypto.Signer
// for the given BCCSP instance and key.
func NewSigner(csp BCCSP, key Key) (crypto.Signer, error) { //SOURCE:bccsp.BCCSP //SOURCE:bccsp.Key
	// Validate arguments
	if csp == nil {
		return nil, errors.New("bccsp instance must be different from nil.")
	}
	if key == nil {
		return nil, errors.New("key must be different from nil.")
	}
	if key.Symmetric() {
		return nil, errors.New("key must be asymmetric.")
	}

	// Marshall the bccsp public key as a crypto.PublicKey
	pub, err := key.PublicKey()
	if err != nil {
		return nil, fmt.Errorf("failed getting public key [%s]", err)
	}

	raw, err := pub.Bytes()
	if err != nil {
		return nil, fmt.Errorf("failed marshalling public key [%s]", err)
	}

	pk, err := DERToPublicKey(raw) //SOURCE:utils.DERToPublicKey
	if err != nil {
		return nil, fmt.Errorf("failed marshalling der to public key [%s]", err)
	}

	return &bccspCryptoSigner{csp, key, pk}, nil
}
// Public returns the public key corresponding to the opaque,
// private key.
func (s *bccspCryptoSigner) Public() crypto.PublicKey {
	return s.pk
}
// Sign signs digest with the private key, possibly using entropy from
// rand. For an RSA key, the resulting signature should be either a
// PKCS#1 v1.5 or PSS signature (as indicated by opts). For an (EC)DSA
// key, it should be a DER-serialised, ASN.1 signature structure.
//
// Hash implements the SignerOpts interface and, in most cases, one can
// simply pass in the hash function used as opts. Sign may also attempt
// to type assert opts to other types in order to obtain algorithm
// specific values. See the documentation in each package for details.
//
// Note that when a signature of a hash of a larger message is needed,
// the caller is responsible for hashing the larger message and passing
// the hash (as digest) and the hash function (as opts) to Sign.
func (s *bccspCryptoSigner) Sign(rand io.Reader, digest []byte, opts crypto.SignerOpts) (signature []byte, err error) {
	return s.csp.Sign(s.key, digest, opts)
}

/*** hyperledger/fabric/common/tools/cryptogen/csp/csp.go ***/
// GeneratePrivateKey creates a private key and stores it in keystorePath
func GeneratePrivateKey(keystorePath string) (Key, //SOURCE:bccsp.GeneratePrivateKey
	crypto.Signer, error) {

	var err error
	var priv Key
	var s crypto.Signer

	opts := &FactoryOpts{ //SOURCE:factory.FactoryOpts
		ProviderName: "SW",
		SwOpts: &SwOpts{ //SOURCE:factory.SwOpts
			HashFamily: "SHA2",
			SecLevel:   256,

			FileKeystore: &FileKeystoreOpts{ //SOURCE:factory.FileKeystoreOpts
				KeyStorePath: keystorePath,
			},
		},
	}
	csp, err := GetBCCSPFromOpts(opts) //SOURCE:factory.GetBCCSPFromOpts
	if err == nil {
		// generate a key
		priv, err = csp.KeyGen(&ECDSAP256KeyGenOpts{Temporary: false}) //SOURCE:bccsp.ECDSAP256KeyGenOpts
		if err == nil {
			// create a crypto.Signer
			s, err = NewSigner(csp, priv) //SOURCE:signer.New
		}
	}
	return priv, s, err
}
/*** hyperledger/fabric/common/tools/cryptogen/csp/csp.go ***/
func GetECPublicKey(priv Key) (*ecdsa.PublicKey, error) {

	// get the public key
	pubKey, err := priv.PublicKey()
	if err != nil {
		return nil, err
	}
	// marshal to bytes
	pubKeyBytes, err := pubKey.Bytes()
	if err != nil {
		return nil, err
	}
	// unmarshal using pkix
	ecPubKey, err := x509.ParsePKIXPublicKey(pubKeyBytes)
	if err != nil {
		return nil, err
	}
	return ecPubKey.(*ecdsa.PublicKey), nil
}
/*** hyperledger/fabric/common/tools/cryptogen/ca/generator.go ***/
type CA struct {
	Name string
	//SignKey  *ecdsa.PrivateKey
	Signer   crypto.Signer
	SignCert *x509.Certificate
}
// NewCA creates an instance of CA and saves the signing key pair in
// baseDir/name
func NewCA(baseDir, org, name string) (*CA, error) {

	var response error
	var ca *CA

	err := os.MkdirAll(baseDir, 0755)
	if err == nil {
		priv, signer, err := GeneratePrivateKey(baseDir) //SOURCE:csp.GeneratePrivateKey
		response = err
		if err == nil {
			// get public signing certificate
			ecPubKey, err := GetECPublicKey(priv) //SOURCE:csp.GetECPublicKey
			response = err
			if err == nil {
				template := x509Template()
				//this is a CA
				template.IsCA = true
				template.KeyUsage |= x509.KeyUsageDigitalSignature |
					x509.KeyUsageKeyEncipherment | x509.KeyUsageCertSign |
					x509.KeyUsageCRLSign
				template.ExtKeyUsage = []x509.ExtKeyUsage{x509.ExtKeyUsageAny}

				//set the organization for the subject
				subject := subjectTemplate()
				subject.Organization = []string{org}
				subject.CommonName = name

				template.Subject = subject
				template.SubjectKeyId = priv.SKI()

				x509Cert, err := genCertificateECDSA(baseDir, name, &template, &template,
					ecPubKey, signer)
				response = err
				if err == nil {
					ca = &CA{
						Name:     name,
						Signer:   signer,
						SignCert: x509Cert,
					}
				}
			}
		}
	}
	return ca, response
}
// SignCertificate creates a signed certificate based on a built-in template
// and saves it in baseDir/name
func (ca *CA) SignCertificate(baseDir, name string, sans []string, pub *ecdsa.PublicKey,
	ku x509.KeyUsage, eku []x509.ExtKeyUsage) (*x509.Certificate, error) {

	template := x509Template()
	template.KeyUsage = ku
	template.ExtKeyUsage = eku

	//set the organization for the subject
	subject := subjectTemplate()
	subject.CommonName = name

	template.Subject = subject
	template.DNSNames = sans

	cert, err := genCertificateECDSA(baseDir, name, &template, ca.SignCert,
		pub, ca.Signer)

	if err != nil {
		return nil, err
	}

	return cert, nil
}
// default template for X509 subject
func subjectTemplate() pkix.Name {
	return pkix.Name{
		Country:  []string{"US"},
		Locality: []string{"San Francisco"},
		Province: []string{"California"},
	}
}
// default template for X509 certificates
func x509Template() x509.Certificate {

	// generate a serial number
	serialNumberLimit := new(big.Int).Lsh(big.NewInt(1), 128)
	serialNumber, _ := rand.Int(rand.Reader, serialNumberLimit)

	// set expiry to around 10 years
	expiry := 3650 * 24 * time.Hour
	// backdate 5 min
	notBefore := time.Now().Add(-5 * time.Minute).UTC()

	//basic template to use
	x509 := x509.Certificate{
		SerialNumber:          serialNumber,
		NotBefore:             notBefore,
		NotAfter:              notBefore.Add(expiry).UTC(),
		BasicConstraintsValid: true,
	}
	return x509

}
// generate a signed X509 certficate using ECDSA
func genCertificateECDSA(baseDir, name string, template, parent *x509.Certificate, pub *ecdsa.PublicKey,
	priv interface{}) (*x509.Certificate, error) {

	//create the x509 public cert
	certBytes, err := x509.CreateCertificate(rand.Reader, template, parent, pub, priv)
	if err != nil {
		return nil, err
	}

	//write cert out to file
	fileName := filepath.Join(baseDir, name+"-cert.pem")
	certFile, err := os.Create(fileName)
	if err != nil {
		return nil, err
	}
	//pem encode the cert
	err = pem.Encode(certFile, &pem.Block{Type: "CERTIFICATE", Bytes: certBytes})
	certFile.Close()
	if err != nil {
		return nil, err
	}

	x509Cert, err := x509.ParseCertificate(certBytes)
	if err != nil {
		return nil, err
	}
	return x509Cert, nil
}

/*** hyperledger/fabric/common/tools/cryptogen/msp/generator.go ***/
func GenerateLocalMSP(baseDir, name string, sans []string, signCA *CA, tlsCA *CA) error { //SOURCE:ca.CA

	// create folder structure
	mspDir := filepath.Join(baseDir, "msp")
	tlsDir := filepath.Join(baseDir, "tls")

	err := createFolderStructure(mspDir, true)
	if err != nil {
		return err
	}

	err = os.MkdirAll(tlsDir, 0755)
	if err != nil {
		return err
	}

	/*
		Create the MSP identity artifacts
	*/
	// get keystore path
	keystore := filepath.Join(mspDir, "keystore")

	// generate private key
	priv, _, err := GeneratePrivateKey(keystore) //SOURCE:csp.GeneratePrivateKey
	if err != nil {
		return err
	}

	// get public key
	ecPubKey, err := GetECPublicKey(priv) //SOURCE:csp.GetECPublicKey
	if err != nil {
		return err
	}
	// generate X509 certificate using signing CA
	cert, err := signCA.SignCertificate(filepath.Join(mspDir, "signcerts"),
		name, []string{}, ecPubKey, x509.KeyUsageDigitalSignature, []x509.ExtKeyUsage{})
	if err != nil {
		return err
	}

	// write artifacts to MSP folders

	// the signing CA certificate goes into cacerts
	err = x509Export(filepath.Join(mspDir, "cacerts", x509Filename(signCA.Name)), signCA.SignCert)
	if err != nil {
		return err
	}
	// the TLS CA certificate goes into tlscacerts
	err = x509Export(filepath.Join(mspDir, "tlscacerts", x509Filename(tlsCA.Name)), tlsCA.SignCert)
	if err != nil {
		return err
	}

	// the signing identity goes into admincerts.
	// This means that the signing identity
	// of this MSP is also an admin of this MSP
	// NOTE: the admincerts folder is going to be
	// cleared up anyway by copyAdminCert, but
	// we leave a valid admin for now for the sake
	// of unit tests
	err = x509Export(filepath.Join(mspDir, "admincerts", x509Filename(name)), cert)
	if err != nil {
		return err
	}

	/*
		Generate the TLS artifacts in the TLS folder
	*/

	// generate private key
	tlsPrivKey, _, err := GeneratePrivateKey(tlsDir) //SOURCE:csp.GeneratePrivateKey
	if err != nil {
		return err
	}
	// get public key
	tlsPubKey, err := GetECPublicKey(tlsPrivKey) //SOURCE:csp.GetECPublicKey
	if err != nil {
		return err
	}
	// generate X509 certificate using TLS CA
	_, err = tlsCA.SignCertificate(filepath.Join(tlsDir),
		name, sans, tlsPubKey, x509.KeyUsageDigitalSignature|x509.KeyUsageKeyEncipherment,
		[]x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth, x509.ExtKeyUsageClientAuth})
	if err != nil {
		return err
	}
	err = x509Export(filepath.Join(tlsDir, "ca.crt"), tlsCA.SignCert)
	if err != nil {
		return err
	}

	// rename the generated TLS X509 cert
	err = os.Rename(filepath.Join(tlsDir, x509Filename(name)),
		filepath.Join(tlsDir, "server.crt"))
	if err != nil {
		return err
	}

	err = keyExport(tlsDir, filepath.Join(tlsDir, "server.key"), tlsPrivKey)
	if err != nil {
		return err
	}

	return nil
}
func GenerateVerifyingMSP(baseDir string, signCA *CA, tlsCA *CA) error { //SOURCE:ca.CA

	// create folder structure and write artifacts to proper locations
	err := createFolderStructure(baseDir, false)
	if err == nil {
		// the signing CA certificate goes into cacerts
		err = x509Export(filepath.Join(baseDir, "cacerts", x509Filename(signCA.Name)), signCA.SignCert)
		if err != nil {
			return err
		}
		// the TLS CA certificate goes into tlscacerts
		err = x509Export(filepath.Join(baseDir, "tlscacerts", x509Filename(tlsCA.Name)), tlsCA.SignCert)
		if err != nil {
			return err
		}
	}

	// create a throwaway cert to act as an admin cert
	// NOTE: the admincerts folder is going to be
	// cleared up anyway by copyAdminCert, but
	// we leave a valid admin for now for the sake
	// of unit tests
	InitFactories(nil) //SOURCE:factory.InitFactories
	bcsp := GetDefault() //SOURCE:factory.GetDefault
	priv, err := bcsp.KeyGen(&ECDSAP256KeyGenOpts{Temporary: true}) //SOURCE:bccsp.ECDSAP256KeyGenOpts
	ecPubKey, err := GetECPublicKey(priv) //SOURCE:csp.GetECPublicKey
	if err != nil {
		return err
	}
	_, err = signCA.SignCertificate(filepath.Join(baseDir, "admincerts"), signCA.Name,
		[]string{""}, ecPubKey, x509.KeyUsageDigitalSignature, []x509.ExtKeyUsage{})
	if err != nil {
		return err
	}

	return nil
}
func createFolderStructure(rootDir string, local bool) error {

	var folders []string
	// create admincerts, cacerts, keystore and signcerts folders
	folders = []string{
		filepath.Join(rootDir, "admincerts"),
		filepath.Join(rootDir, "cacerts"),
		filepath.Join(rootDir, "tlscacerts"),
	}
	if local {
		folders = append(folders, filepath.Join(rootDir, "keystore"),
			filepath.Join(rootDir, "signcerts"))
	}

	for _, folder := range folders {
		err := os.MkdirAll(folder, 0755)
		if err != nil {
			return err
		}
	}

	return nil
}
func x509Filename(name string) string {
	return name + "-cert.pem"
}
func x509Export(path string, cert *x509.Certificate) error {
	return pemExport(path, "CERTIFICATE", cert.Raw)
}
func keyExport(keystore, output string, key Key) error { //SOURCE:bccsp.Key
	id := hex.EncodeToString(key.SKI())

	return os.Rename(filepath.Join(keystore, id+"_sk"), output)
}
func pemExport(path, pemType string, bytes []byte) error {
	//write pem out to file
	file, err := os.Create(path)
	if err != nil {
		return err
	}
	defer file.Close()

	return pem.Encode(file, &pem.Block{Type: pemType, Bytes: bytes})
}

/*** hyperledger/fabric/common/tools/cryptogen/metadata/metadata.go ***/
// package-scoped variables
// Package version
var Version string
// package-scoped constants
// Program name
const ProgramName = "cryptogen"
func GetVersionInfo() string {
	if Version == "" {
		Version = "development build"
	}

	return fmt.Sprintf("%s:\n Version: %s\n Go version: %s\n OS/Arch: %s",
		ProgramName, Version, runtime.Version(),
		fmt.Sprintf("%s/%s", runtime.GOOS, runtime.GOARCH))
}



/*
*
*
ORIGINAL CRYPTOGEN MAIN FILE
*
*
*/
const (
	userBaseName            = "User"
	adminBaseName           = "Admin"
	defaultHostnameTemplate = "{{.Prefix}}{{.Index}}"
	defaultCNTemplate       = "{{.Hostname}}.{{.Domain}}"
)

type HostnameData struct {
	Prefix string
	Index  int
	Domain string
}

type SpecData struct {
	Hostname   string
	Domain     string
	CommonName string
}

type NodeTemplate struct {
	Count    int      `yaml:"Count"`
	Start    int      `yaml:"Start"`
	Hostname string   `yaml:"Hostname"`
	SANS     []string `yaml:"SANS"`
}

type NodeSpec struct {
	Hostname   string   `yaml:"Hostname"`
	CommonName string   `yaml:"CommonName"`
	SANS       []string `yaml:"SANS"`
}

type UsersSpec struct {
	Count int `yaml:"Count"`
}

type OrgSpec struct {
	Name     string       `yaml:"Name"`
	Domain   string       `yaml:"Domain"`
	CA       NodeSpec     `yaml:"CA"`
	Template NodeTemplate `yaml:"Template"`
	Specs    []NodeSpec   `yaml:"Specs"`
	Users    UsersSpec    `yaml:"Users"`
}

type Config struct {
	OrdererOrgs []OrgSpec `yaml:"OrdererOrgs"`
	PeerOrgs    []OrgSpec `yaml:"PeerOrgs"`
}

var defaultConfig = `
# ---------------------------------------------------------------------------
# "OrdererOrgs" - Definition of organizations managing orderer nodes
# ---------------------------------------------------------------------------
OrdererOrgs:
  # ---------------------------------------------------------------------------
  # Orderer
  # ---------------------------------------------------------------------------
  - Name: Orderer
    Domain: example.com
    # ---------------------------------------------------------------------------
    # "Specs" - See PeerOrgs below for complete description
    # ---------------------------------------------------------------------------
    Specs:
      - Hostname: orderer
# ---------------------------------------------------------------------------
# "PeerOrgs" - Definition of organizations managing peer nodes
# ---------------------------------------------------------------------------
PeerOrgs:
  # ---------------------------------------------------------------------------
  # Org1
  # ---------------------------------------------------------------------------
  - Name: Org1
    Domain: org1.example.com
    # ---------------------------------------------------------------------------
    # "CA"
    # ---------------------------------------------------------------------------
    # Uncomment this section to enable the explicit definition of the CA for this
    # organization.  This entry is a Spec.  See "Specs" section below for details.
    # ---------------------------------------------------------------------------
    # CA:
    #    Hostname: ca # implicitly ca.org1.example.com
    # ---------------------------------------------------------------------------
    # "Specs"
    # ---------------------------------------------------------------------------
    # Uncomment this section to enable the explicit definition of hosts in your
    # configuration.  Most users will want to use Template, below
    #
    # Specs is an array of Spec entries.  Each Spec entry consists of two fields:
    #   - Hostname:   (Required) The desired hostname, sans the domain.
    #   - CommonName: (Optional) Specifies the template or explicit override for
    #                 the CN.  By default, this is the template:
    #
    #                              "{{.Hostname}}.{{.Domain}}"
    #
    #                 which obtains its values from the Spec.Hostname and
    #                 Org.Domain, respectively.
    #   - SANS:       (Optional) Specifies one or more Subject Alternative Names
    #                 the be set in the resulting x509.  Accepts template
    #                 variables {{.Hostname}}, {{.Domain}}, {{.CommonName}}
    #                 NOTE: Two implicit entries are created for you:
    #                     - {{ .CommonName }}
    #                     - {{ .Hostname }}
    # ---------------------------------------------------------------------------
    # Specs:
    #   - Hostname: foo # implicitly "foo.org1.example.com"
    #     CommonName: foo27.org5.example.com # overrides Hostname-based FQDN set above
    #     SANS:
    #       - "bar.{{.Domain}}"
    #       - "altfoo.{{.Domain}}"
    #       - "{{.Hostname}}.org6.net"
    #   - Hostname: bar
    #   - Hostname: baz
    # ---------------------------------------------------------------------------
    # "Template"
    # ---------------------------------------------------------------------------
    # Allows for the definition of 1 or more hosts that are created sequentially
    # from a template. By default, this looks like "peer%d" from 0 to Count-1.
    # You may override the number of nodes (Count), the starting index (Start)
    # or the template used to construct the name (Hostname).
    #
    # Note: Template and Specs are not mutually exclusive.  You may define both
    # sections and the aggregate nodes will be created for you.  Take care with
    # name collisions
    # ---------------------------------------------------------------------------
    Template:
      Count: 1
      # Start: 5
      # Hostname: {{.Prefix}}{{.Index}} # default
      # SANS:
      #   - "{{.Hostname}}.alt.{{.Domain}}"
    # ---------------------------------------------------------------------------
    # "Users"
    # ---------------------------------------------------------------------------
    # Count: The number of user accounts _in addition_ to Admin
    # ---------------------------------------------------------------------------
    Users:
      Count: 1
  # ---------------------------------------------------------------------------
  # Org2: See "Org1" for full specification
  # ---------------------------------------------------------------------------
  - Name: Org2
    Domain: org2.example.com
    Template:
      Count: 1
    Users:
      Count: 1
`

//command line flags
var (
	app = kingpin.New("cryptogen", "Utility for generating Hyperledger Fabric key material") //SOURCE: kingpin.New

	gen        = app.Command("generate", "Generate key material")
	outputDir  = gen.Flag("output", "The output directory in which to place artifacts").Default("crypto-config").String()
	configFile = gen.Flag("config", "The configuration template to use").File()

	showtemplate = app.Command("showtemplate", "Show the default configuration template")

	version = app.Command("version", "Show version information")
)

func main() {
	kingpin.Version("0.0.1") //TODO //SOURCE: kingpin.Version
	switch kingpin.MustParse(app.Parse(os.Args[1:])) { //SOURCE: kingpin.MustParse

	// "generate" command
	case gen.FullCommand():
		generate()

	// "showtemplate" command
	case showtemplate.FullCommand():
		fmt.Print(defaultConfig)
		os.Exit(0)

	// "version" command
	case version.FullCommand():
		printVersion()
	}

}

func getConfig() (*Config, error) {
	var configData string

	if *configFile != nil {
		data, err := ioutil.ReadAll(*configFile)
		if err != nil {
			return nil, fmt.Errorf("Error reading configuration: %s", err)
		}

		configData = string(data)
	} else {
		configData = defaultConfig
	}
	config := &Config{}
	err := yaml.Unmarshal([]byte(configData), &config)
	if err != nil {
		return nil, fmt.Errorf("Error Unmarshaling YAML: %s", err)
	}
    fmt.Println("config:")
    fmt.Println(config)
	return config, nil
}

func generate() {

	config, err := getConfig()
	if err != nil {
		fmt.Printf("Error reading config: %s", err)
		os.Exit(-1)
	}

	for _, orgSpec := range config.PeerOrgs {
        fmt.Println(orgSpec)
		err = renderOrgSpec(&orgSpec, "peer")
        //Default:{Org1 org1.example.com {ca ca.org1.example.com [ca.org1.example.com ca]} {1 0  []} [{peer0 peer0.org1.example.com [peer0.org1.example.com peer0]}] {1}}
        if err != nil {
			fmt.Printf("Error processing peer configuration: %s", err)
			os.Exit(-1)
		}
		generatePeerOrg(*outputDir, orgSpec)
	}

	for _, orgSpec := range config.OrdererOrgs {
        fmt.Println(orgSpec)
		err = renderOrgSpec(&orgSpec, "orderer") //EDIT:added "err = "
        //Default:{Orderer example.com {ca ca.example.com [ca.example.com ca]} {0 0  []} [{orderer orderer.example.com [orderer.example.com orderer]}] {0}}
		if err != nil {
			fmt.Printf("Error processing orderer configuration: %s", err)
			os.Exit(-1)
		}
		generateOrdererOrg(*outputDir, orgSpec)
	}
}

func parseTemplate(input string, data interface{}) (string, error) {

	t, err := template.New("parse").Parse(input) //NOTE:'New("parse")' gives a name to the parsed template (if later reference is needed)
	if err != nil {
		return "", fmt.Errorf("Error parsing template: %s", err)
	}

	output := new(bytes.Buffer)
	err = t.Execute(output, data) //NOTE:Execute applies the inputs to the template ("{{.Prefix}}{{.Index}}")
	if err != nil {
		return "", fmt.Errorf("Error executing template: %s", err)
	}

	return output.String(), nil
}

func parseTemplateWithDefault(input, defaultInput string, data interface{}) (string, error) {

	// Use the default if the input is an empty string
	if len(input) == 0 {
		input = defaultInput
	}

	return parseTemplate(input, data)
}

func renderNodeSpec(domain string, spec *NodeSpec) error {
	data := SpecData{
		Hostname: spec.Hostname,
		Domain:   domain,
	}

	// Process our CommonName
	cn, err := parseTemplateWithDefault(spec.CommonName, defaultCNTemplate, data) //NOTE:default template:"{{.Hostname}}.{{.Domain}}"
	if err != nil {
		return err
	}

	spec.CommonName = cn
	data.CommonName = cn

	// Save off our original, unprocessed SANS entries
	origSANS := spec.SANS

	// Set our implicit SANS entries for CN/Hostname
	spec.SANS = []string{cn, spec.Hostname}

	// Finally, process any remaining SANS entries
	for _, _san := range origSANS {
		san, err := parseTemplate(_san, data)
		if err != nil {
			return err
		}

		spec.SANS = append(spec.SANS, san)
	}

	return nil
}

func renderOrgSpec(orgSpec *OrgSpec, prefix string) error {
    fmt.Println("START renderOrgSpec:")
	// First process all of our templated nodes
	for i := 0; i < orgSpec.Template.Count; i++ {
		data := HostnameData{
			Prefix: prefix,
			Index:  i + orgSpec.Template.Start,
			Domain: orgSpec.Domain,
		}

		hostname, err := parseTemplateWithDefault(orgSpec.Template.Hostname, defaultHostnameTemplate, data) //NOTE:Default Template:"{{.Prefix}}{{.Index}}"
		if err != nil {
			return err
		}
		spec := NodeSpec{
			Hostname: hostname,
			SANS:     orgSpec.Template.SANS,
		}
		orgSpec.Specs = append(orgSpec.Specs, spec)
	}

	// Touch up all general node-specs to add the domain
	for idx, spec := range orgSpec.Specs {
		err := renderNodeSpec(orgSpec.Domain, &spec)
        //"{{.Hostname}}.{{.Domain}}" Default:{peer0 peer0.org1.example.com [peer0.org1.example.com peer0]}
        //Default:{orderer orderer.example.com [orderer.example.com orderer]}
		if err != nil {
			return err
		}
		orgSpec.Specs[idx] = spec
	}

	// Process the CA node-spec in the same manner
	if len(orgSpec.CA.Hostname) == 0 {
		orgSpec.CA.Hostname = "ca"
	}
	err := renderNodeSpec(orgSpec.Domain, &orgSpec.CA)
	if err != nil {
		return err
	}
	return nil
}

func generatePeerOrg(baseDir string, orgSpec OrgSpec) {
    fmt.Println(orgSpec)
	orgName := orgSpec.Domain

	fmt.Println(orgName)
	// generate CAs
	orgDir := filepath.Join(baseDir, "peerOrganizations", orgName)
	caDir := filepath.Join(orgDir, "ca")
	tlsCADir := filepath.Join(orgDir, "tlsca")
	mspDir := filepath.Join(orgDir, "msp")
	peersDir := filepath.Join(orgDir, "peers")
	usersDir := filepath.Join(orgDir, "users")
	adminCertsDir := filepath.Join(mspDir, "admincerts")
	// generate signing CA
	signCA, err := NewCA(caDir, orgName, orgSpec.CA.CommonName) //SOURCE:ca.NewCA
	if err != nil {
		fmt.Printf("Error generating signCA for org %s:\n%v\n", orgName, err)
		os.Exit(1)
	}
	// generate TLS CA
	tlsCA, err := NewCA(tlsCADir, orgName, "tls"+orgSpec.CA.CommonName) //SOURCE:ca.NewCA
	if err != nil {
		fmt.Printf("Error generating tlsCA for org %s:\n%v\n", orgName, err)
		os.Exit(1)
	}

	err = GenerateVerifyingMSP(mspDir, signCA, tlsCA) //SOURCE:msp.GenerateVerifyingMSP
	if err != nil {
		fmt.Printf("Error generating MSP for org %s:\n%v\n", orgName, err)
		os.Exit(1)
	}

	generateNodes(peersDir, orgSpec.Specs, signCA, tlsCA)

	// TODO: add ability to specify usernames
	users := []NodeSpec{}
	for j := 1; j <= orgSpec.Users.Count; j++ {
		user := NodeSpec{
			CommonName: fmt.Sprintf("%s%d@%s", userBaseName, j, orgName),
		}

		users = append(users, user)
	}
	// add an admin user
	adminUser := NodeSpec{
		CommonName: fmt.Sprintf("%s@%s", adminBaseName, orgName),
	}

	users = append(users, adminUser)
	generateNodes(usersDir, users, signCA, tlsCA)

	// copy the admin cert to the org's MSP admincerts
	err = copyAdminCert(usersDir, adminCertsDir, adminUser.CommonName)
	if err != nil {
		fmt.Printf("Error copying admin cert for org %s:\n%v\n",
			orgName, err)
		os.Exit(1)
	}

	// copy the admin cert to each of the org's peer's MSP admincerts
	for _, spec := range orgSpec.Specs {
		err = copyAdminCert(usersDir,
			filepath.Join(peersDir, spec.CommonName, "msp", "admincerts"), adminUser.CommonName)
		if err != nil {
			fmt.Printf("Error copying admin cert for org %s peer %s:\n%v\n",
				orgName, spec.CommonName, err)
			os.Exit(1)
		}
	}
}

func copyAdminCert(usersDir, adminCertsDir, adminUserName string) error {
	// delete the contents of admincerts
	err := os.RemoveAll(adminCertsDir)
	if err != nil {
		return err
	}
	// recreate the admincerts directory
	err = os.MkdirAll(adminCertsDir, 0755)
	if err != nil {
		return err
	}
	err = copyFile(filepath.Join(usersDir, adminUserName, "msp", "signcerts",
		adminUserName+"-cert.pem"), filepath.Join(adminCertsDir,
		adminUserName+"-cert.pem"))
	if err != nil {
		return err
	}
	return nil

}

func generateNodes(baseDir string, nodes []NodeSpec, signCA *CA, tlsCA *CA) { //SOURCE:ca.generateNodes

	for _, node := range nodes {
		nodeDir := filepath.Join(baseDir, node.CommonName)
		err := GenerateLocalMSP(nodeDir, node.CommonName, node.SANS, signCA, tlsCA) //SOURCE:msp.GenerateLocalMSP
		if err != nil {
			fmt.Printf("Error generating local MSP for %s:\n%v\n", node, err)
			os.Exit(1)
		}
	}
}

func generateOrdererOrg(baseDir string, orgSpec OrgSpec) {
    fmt.Println(orgSpec)
	orgName := orgSpec.Domain

	fmt.Println(orgName)
	// generate CAs
	orgDir := filepath.Join(baseDir, "ordererOrganizations", orgName)
	caDir := filepath.Join(orgDir, "ca")
	tlsCADir := filepath.Join(orgDir, "tlsca")
	mspDir := filepath.Join(orgDir, "msp")
	orderersDir := filepath.Join(orgDir, "orderers")
	usersDir := filepath.Join(orgDir, "users")
	adminCertsDir := filepath.Join(mspDir, "admincerts")
	// generate signing CA
	signCA, err := NewCA(caDir, orgName, orgSpec.CA.CommonName) //SOURCE:ca.NewCA
	if err != nil {
		fmt.Printf("Error generating signCA for org %s:\n%v\n", orgName, err)
		os.Exit(1)
	}
	// generate TLS CA
	tlsCA, err := NewCA(tlsCADir, orgName, "tls"+orgSpec.CA.CommonName) //SOURCE:ca.NewCA
	if err != nil {
		fmt.Printf("Error generating tlsCA for org %s:\n%v\n", orgName, err)
		os.Exit(1)
	}

	err = GenerateVerifyingMSP(mspDir, signCA, tlsCA) //SOURCE:msp.GenerateVerifyingMSP
	if err != nil {
		fmt.Printf("Error generating MSP for org %s:\n%v\n", orgName, err)
		os.Exit(1)
	}

	generateNodes(orderersDir, orgSpec.Specs, signCA, tlsCA)

	adminUser := NodeSpec{
		CommonName: fmt.Sprintf("%s@%s", adminBaseName, orgName),
	}

	// generate an admin for the orderer org
	users := []NodeSpec{}
	// add an admin user
	users = append(users, adminUser)
	generateNodes(usersDir, users, signCA, tlsCA)

	// copy the admin cert to the org's MSP admincerts
	err = copyAdminCert(usersDir, adminCertsDir, adminUser.CommonName)
	if err != nil {
		fmt.Printf("Error copying admin cert for org %s:\n%v\n",
			orgName, err)
		os.Exit(1)
	}

	// copy the admin cert to each of the org's orderers's MSP admincerts
	for _, spec := range orgSpec.Specs {
		err = copyAdminCert(usersDir,
			filepath.Join(orderersDir, spec.CommonName, "msp", "admincerts"), adminUser.CommonName)
		if err != nil {
			fmt.Printf("Error copying admin cert for org %s orderer %s:\n%v\n",
				orgName, spec.CommonName, err)
			os.Exit(1)
		}
	}

}

func copyFile(src, dst string) error {
	in, err := os.Open(src)
	if err != nil {
		return err
	}
	defer in.Close()
	out, err := os.Create(dst)
	if err != nil {
		return err
	}
	defer out.Close()
	_, err = io.Copy(out, in)
	cerr := out.Close()
	if err != nil {
		return err
	}
	return cerr
}

func printVersion() {
	fmt.Println(GetVersionInfo()) //SOURCE:metadata.GetVersionInfo()
}
