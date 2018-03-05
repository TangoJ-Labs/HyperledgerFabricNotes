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

package main

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
	"encoding/json"
    "encoding/pem"
    "errors"
	"flag"
	"fmt"
    "hash"
    "io"
	"io/ioutil"
    "math"
    "math/big"
	"os"
    "path/filepath"
    "reflect"
    "regexp"
    "runtime"
	"strconv"
	"strings"
    "sync"
    "time"

	// "github.com/hyperledger/fabric/bccsp/factory"
	// "github.com/hyperledger/fabric/common/config"
	// mspconfig "github.com/hyperledger/fabric/common/config/msp"
	// "github.com/hyperledger/fabric/common/configtx"
	// "github.com/hyperledger/fabric/common/configtx/tool/configtxgen/metadata"
	// genesisconfig "github.com/hyperledger/fabric/common/configtx/tool/localconfig"
	// "github.com/hyperledger/fabric/common/configtx/tool/provisional"
	// "github.com/hyperledger/fabric/common/flogging"
	// cb "github.com/hyperledger/fabric/protos/common"
	// pb "github.com/hyperledger/fabric/protos/peer"
	// "github.com/hyperledger/fabric/protos/utils"

    "github.com/golang/protobuf/jsonpb"
	"github.com/golang/protobuf/proto"
    "github.com/golang/protobuf/ptypes/timestamp"
	logging "github.com/op/go-logging"



    "golang.org/x/crypto/sha3"
    "gopkg.in/yaml.v2"
    // google_protobuf "github.com/golang/protobuf/ptypes/timestamp"

    "github.com/Shopify/sarama"
    version "github.com/hashicorp/go-version"
    "github.com/miekg/pkcs11"
    "github.com/mitchellh/mapstructure"
    "github.com/spf13/viper"
)


/*** fabric/common/viperutil/config_util.go ***/
type viperGetter func(key string) interface{}
func getKeysRecursively(base string, getKey viperGetter, nodeKeys map[string]interface{}) map[string]interface{} {
	result := make(map[string]interface{})
	for key := range nodeKeys {
		fqKey := base + key
		val := getKey(fqKey)
		if m, ok := val.(map[interface{}]interface{}); ok {
			logger.Debugf("Found map[interface{}]interface{} value for %s", fqKey)
			tmp := make(map[string]interface{})
			for ik, iv := range m {
				cik, ok := ik.(string)
				if !ok {
					panic("Non string key-entry")
				}
				tmp[cik] = iv
			}
			result[key] = getKeysRecursively(fqKey+".", getKey, tmp)
		} else if m, ok := val.(map[string]interface{}); ok {
			logger.Debugf("Found map[string]interface{} value for %s", fqKey)
			result[key] = getKeysRecursively(fqKey+".", getKey, m)
		} else if m, ok := unmarshalJSON(val); ok {
			logger.Debugf("Found real value for %s setting to map[string]string %v", fqKey, m)
			result[key] = m
		} else {
			if val == nil {
				fileSubKey := fqKey + ".File"
				fileVal := getKey(fileSubKey)
				if fileVal != nil {
					result[key] = map[string]interface{}{"File": fileVal}
					continue
				}
			}
			logger.Debugf("Found real value for %s setting to %T %v", fqKey, val, val)
			result[key] = val

		}
	}
	return result
}
func unmarshalJSON(val interface{}) (map[string]string, bool) {
	mp := map[string]string{}
	s, ok := val.(string)
	if !ok {
		logger.Debugf("Unmarshal JSON: value is not a string: %v", val)
		return nil, false
	}
	err := json.Unmarshal([]byte(s), &mp)
	if err != nil {
		logger.Debugf("Unmarshal JSON: value cannot be unmarshalled: %s", err)
		return nil, false
	}
	return mp, true
}
// customDecodeHook adds the additional functions of parsing durations from strings
// as well as parsing strings of the format "[thing1, thing2, thing3]" into string slices
// Note that whitespace around slice elements is removed
func customDecodeHook() mapstructure.DecodeHookFunc {
	durationHook := mapstructure.StringToTimeDurationHookFunc()
	return func(f reflect.Type, t reflect.Type, data interface{}) (interface{}, error) {
		dur, err := mapstructure.DecodeHookExec(durationHook, f, t, data)
		if err == nil {
			if _, ok := dur.(time.Duration); ok {
				return dur, nil
			}
		}

		if f.Kind() != reflect.String {
			return data, nil
		}

		raw := data.(string)
		l := len(raw)
		if l > 1 && raw[0] == '[' && raw[l-1] == ']' {
			slice := strings.Split(raw[1:l-1], ",")
			for i, v := range slice {
				slice[i] = strings.TrimSpace(v)
			}
			return slice, nil
		}

		return data, nil
	}
}
func byteSizeDecodeHook() mapstructure.DecodeHookFunc {
	return func(f reflect.Kind, t reflect.Kind, data interface{}) (interface{}, error) {
		if f != reflect.String || t != reflect.Uint32 {
			return data, nil
		}
		raw := data.(string)
		if raw == "" {
			return data, nil
		}
		var re = regexp.MustCompile(`^(?P<size>[0-9]+)\s*(?i)(?P<unit>(k|m|g))b?$`)
		if re.MatchString(raw) {
			size, err := strconv.ParseUint(re.ReplaceAllString(raw, "${size}"), 0, 64)
			if err != nil {
				return data, nil
			}
			unit := re.ReplaceAllString(raw, "${unit}")
			switch strings.ToLower(unit) {
			case "g":
				size = size << 10
				fallthrough
			case "m":
				size = size << 10
				fallthrough
			case "k":
				size = size << 10
			}
			if size > math.MaxUint32 {
				return size, fmt.Errorf("value '%s' overflows uint32", raw)
			}
			return size, nil
		}
		return data, nil
	}
}
func stringFromFileDecodeHook() mapstructure.DecodeHookFunc {
	return func(f reflect.Kind, t reflect.Kind, data interface{}) (interface{}, error) {
		// "to" type should be string
		if t != reflect.String {
			return data, nil
		}
		// "from" type should be map
		if f != reflect.Map {
			return data, nil
		}
		v := reflect.ValueOf(data)
		switch v.Kind() {
		case reflect.String:
			return data, nil
		case reflect.Map:
			d := data.(map[string]interface{})
			fileName, ok := d["File"]
			if !ok {
				fileName, ok = d["file"]
			}
			switch {
			case ok && fileName != nil:
				bytes, err := ioutil.ReadFile(fileName.(string))
				if err != nil {
					return data, err
				}
				return string(bytes), nil
			case ok:
				// fileName was nil
				return nil, fmt.Errorf("Value of File: was nil")
			}
		}
		return data, nil
	}
}
func pemBlocksFromFileDecodeHook() mapstructure.DecodeHookFunc {
	return func(f reflect.Kind, t reflect.Kind, data interface{}) (interface{}, error) {
		// "to" type should be string
		if t != reflect.Slice {
			return data, nil
		}
		// "from" type should be map
		if f != reflect.Map {
			return data, nil
		}
		v := reflect.ValueOf(data)
		switch v.Kind() {
		case reflect.String:
			return data, nil
		case reflect.Map:
			var fileName string
			var ok bool
			switch d := data.(type) {
			case map[string]string:
				fileName, ok = d["File"]
				if !ok {
					fileName, ok = d["file"]
				}
			case map[string]interface{}:
				var fileI interface{}
				fileI, ok = d["File"]
				if !ok {
					fileI, _ = d["file"]
				}
				fileName, ok = fileI.(string)
			}

			switch {
			case ok && fileName != "":
				var result []string
				bytes, err := ioutil.ReadFile(fileName)
				if err != nil {
					return data, err
				}
				for len(bytes) > 0 {
					var block *pem.Block
					block, bytes = pem.Decode(bytes)
					if block == nil {
						break
					}
					if block.Type != "CERTIFICATE" || len(block.Headers) != 0 {
						continue
					}
					result = append(result, string(pem.EncodeToMemory(block)))
				}
				return result, nil
			case ok:
				// fileName was nil
				return nil, fmt.Errorf("Value of File: was nil")
			}
		}
		return data, nil
	}
}
var kafkaVersionConstraints map[sarama.KafkaVersion]version.Constraints
func initKafkaVersionConstraints() { //WAS:init()
	kafkaVersionConstraints = make(map[sarama.KafkaVersion]version.Constraints)
	kafkaVersionConstraints[sarama.V0_8_2_0], _ = version.NewConstraint(">=0.8.2,<0.8.2.1")
	kafkaVersionConstraints[sarama.V0_8_2_1], _ = version.NewConstraint(">=0.8.2.1,<0.8.2.2")
	kafkaVersionConstraints[sarama.V0_8_2_2], _ = version.NewConstraint(">=0.8.2.2,<0.9.0.0")
	kafkaVersionConstraints[sarama.V0_9_0_0], _ = version.NewConstraint(">=0.9.0.0,<0.9.0.1")
	kafkaVersionConstraints[sarama.V0_9_0_1], _ = version.NewConstraint(">=0.9.0.1,<0.10.0.0")
	kafkaVersionConstraints[sarama.V0_10_0_0], _ = version.NewConstraint(">=0.10.0.0,<0.10.0.1")
	kafkaVersionConstraints[sarama.V0_10_0_1], _ = version.NewConstraint(">=0.10.0.1,<0.10.1.0")
	kafkaVersionConstraints[sarama.V0_10_1_0], _ = version.NewConstraint(">=0.10.1.0,<0.10.2.0")
	kafkaVersionConstraints[sarama.V0_10_2_0], _ = version.NewConstraint(">=0.10.2.0,<0.11.0.0")
}
func kafkaVersionDecodeHook() mapstructure.DecodeHookFunc {
	return func(f reflect.Type, t reflect.Type, data interface{}) (interface{}, error) {
		if f.Kind() != reflect.String || t != reflect.TypeOf(sarama.KafkaVersion{}) {
			return data, nil
		}

		v, err := version.NewVersion(data.(string))
		if err != nil {
			return nil, fmt.Errorf("Unable to parse Kafka version: %s", err)
		}

        initKafkaVersionConstraints() //ADDED
		for kafkaVersion, constraints := range kafkaVersionConstraints {
			if constraints.Check(v) {
				return kafkaVersion, nil
			}
		}

		return nil, fmt.Errorf("Unsupported Kafka version: '%s'", data)
	}
}
// EnhancedExactUnmarshal is intended to unmarshal a config file into a structure
// producing error when extraneous variables are introduced and supporting
// the time.Duration type
func EnhancedExactUnmarshal(v *viper.Viper, output interface{}) error {
	// AllKeys doesn't actually return all keys, it only returns the base ones
	baseKeys := v.AllSettings()
	getterWithClass := func(key string) interface{} { return v.Get(key) } // hide receiver
	leafKeys := getKeysRecursively("", getterWithClass, baseKeys)

	logger.Debugf("%+v", leafKeys)
	config := &mapstructure.DecoderConfig{
		ErrorUnused:      true,
		Metadata:         nil,
		Result:           output,
		WeaklyTypedInput: true,
		DecodeHook: mapstructure.ComposeDecodeHookFunc(
			customDecodeHook(),
			byteSizeDecodeHook(),
			stringFromFileDecodeHook(),
			pemBlocksFromFileDecodeHook(),
			kafkaVersionDecodeHook(),
		),
	}

	decoder, err := mapstructure.NewDecoder(config)
	if err != nil {
		return err
	}
	return decoder.Decode(leafKeys)
}

/*** fabric/core/config/config.go ***/
func dirExists(path string) bool {
	_, err := os.Stat(path)
	return err == nil
}
func addConfigPath(v *viper.Viper, p string) {
	if v != nil {
		v.AddConfigPath(p)
	} else {
		viper.AddConfigPath(p)
	}
}
//----------------------------------------------------------------------------------
// GetDevConfigDir()
//----------------------------------------------------------------------------------
// Returns the path to the default configuration that is maintained with the source
// tree.  Only valid to call from a test/development context.
//----------------------------------------------------------------------------------
func GetDevConfigDir() (string, error) {
	gopath := os.Getenv("GOPATH")
	if gopath == "" {
		return "", fmt.Errorf("GOPATH not set")
	}

	for _, p := range filepath.SplitList(gopath) {
		devPath := filepath.Join(p, "src/github.com/hyperledger/fabric/sampleconfig")
		if !dirExists(devPath) {
			continue
		}

		return devPath, nil
	}

	return "", fmt.Errorf("DevConfigDir not found in %s", gopath)
}
//----------------------------------------------------------------------------------
// TranslatePath()
//----------------------------------------------------------------------------------
// Translates a relative path into a fully qualified path relative to the config
// file that specified it.  Absolute paths are passed unscathed.
//----------------------------------------------------------------------------------
func TranslatePath(base, p string) string {
	if filepath.IsAbs(p) {
		return p
	}

	return filepath.Join(base, p)
}
//----------------------------------------------------------------------------------
// TranslatePathInPlace()
//----------------------------------------------------------------------------------
// Translates a relative path into a fully qualified path in-place (updating the
// pointer) relative to the config file that specified it.  Absolute paths are
// passed unscathed.
//----------------------------------------------------------------------------------
func TranslatePathInPlace(base string, p *string) {
	*p = TranslatePath(base, *p)
}
const OfficialPath = "/etc/hyperledger/fabric"
//----------------------------------------------------------------------------------
// InitViper()
//----------------------------------------------------------------------------------
// Performs basic initialization of our viper-based configuration layer.
// Primary thrust is to establish the paths that should be consulted to find
// the configuration we need.  If v == nil, we will initialize the global
// Viper instance
//----------------------------------------------------------------------------------
func InitViper(v *viper.Viper, configName string) error {
	var altPath = os.Getenv("FABRIC_CFG_PATH")
	if altPath != "" {
		// If the user has overridden the path with an envvar, its the only path
		// we will consider
		addConfigPath(v, altPath)
	} else {
		// If we get here, we should use the default paths in priority order:
		//
		// *) CWD
		// *) The $GOPATH based development tree
		// *) /etc/hyperledger/fabric
		//

		// CWD
		addConfigPath(v, "./")

		// DevConfigPath
		err := AddDevConfigPath(v)
		if err != nil {
			return err
		}

		// And finally, the official path
		if dirExists(OfficialPath) {
			addConfigPath(v, OfficialPath)
		}
	}

	// Now set the configuration file.
	if v != nil {
		v.SetConfigName(configName)
	} else {
		viper.SetConfigName(configName)
	}

	return nil
}
//----------------------------------------------------------------------------------
// AddDevConfigPath()
//----------------------------------------------------------------------------------
// Helper utility that automatically adds our DevConfigDir to the viper path
//----------------------------------------------------------------------------------
func AddDevConfigPath(v *viper.Viper) error {
	devPath, err := GetDevConfigDir()
	if err != nil {
		return err
	}

	addConfigPath(v, devPath)

	return nil
}

/*** fabric/common/configtx/tool/localconfig/config.go ***/
const (
    // Prefix identifies the prefix for the configtxgen-related ENV vars.
	Prefix string = "CONFIGTX"
	// SampleInsecureProfile references the sample profile which does not include any MSPs and uses solo for ordering.
	SampleInsecureProfile = "SampleInsecureSolo"
	// AdminRoleAdminPrincipal is set as AdminRole to cause the MSP role of type Admin to be used as the admin principal default
	AdminRoleAdminPrincipal = "Role.ADMIN"
)
// TopLevel consists of the structs used by the configtxgen tool.
type TopLevel struct {
	Profiles      map[string]*Profile `yaml:"Profiles"`
	Organizations []*Organization     `yaml:"Organizations"`
	Application   *Application        `yaml:"Application"`
	Orderer       *Orderer            `yaml:"Orderer"`
}
// Profile encodes orderer/application configuration combinations for the configtxgen tool.
type Profile struct {
	Consortium  string                 `yaml:"Consortium"`
	Application *Application           `yaml:"Application"`
	Orderer     *Orderer               `yaml:"Orderer"`
	Consortiums map[string]*Consortium `yaml:"Consortiums"`
}
// Consortium represents a group of organizations which may create channels with eachother
type Consortium struct {
	Organizations []*Organization `yaml:"Organizations"`
}
// Application encodes the application-level configuration needed in config transactions.
type Application struct {
	Organizations []*Organization `yaml:"Organizations"`
}
// Organization encodes the organization-level configuration needed in config transactions.
type Organization struct {
	Name           string `yaml:"Name"`
	ID             string `yaml:"ID"`
	MSPDir         string `yaml:"MSPDir"`
	AdminPrincipal string `yaml:"AdminPrincipal"`

	// Note: Viper deserialization does not seem to care for
	// embedding of types, so we use one organization struct
	// for both orderers and applications.
	AnchorPeers []*AnchorPeer `yaml:"AnchorPeers"`
}
// AnchorPeer encodes the necessary fields to identify an anchor peer.
type AnchorPeer struct {
	Host string `yaml:"Host"`
	Port int    `yaml:"Port"`
}
// Orderer contains configuration which is used for the
// bootstrapping of an orderer by the provisional bootstrapper.
type Orderer struct {
	OrdererType   string          `yaml:"OrdererType"`
	Addresses     []string        `yaml:"Addresses"`
	BatchTimeout  time.Duration   `yaml:"BatchTimeout"`
	BatchSize     BatchSize       `yaml:"BatchSize"`
	Kafka         Kafka           `yaml:"Kafka"`
	Organizations []*Organization `yaml:"Organizations"`
	MaxChannels   uint64          `yaml:"MaxChannels"`
}
// BatchSize contains configuration affecting the size of batches.
type BatchSize struct {
	MaxMessageCount   uint32 `yaml:"MaxMessageSize"`
	AbsoluteMaxBytes  uint32 `yaml:"AbsoluteMaxBytes"`
	PreferredMaxBytes uint32 `yaml:"PreferredMaxBytes"`
}
// Kafka contains configuration for the Kafka-based orderer.
type Kafka struct {
	Brokers []string `yaml:"Brokers"`
}
var genesisDefaults = TopLevel{
	Orderer: &Orderer{
		OrdererType:  "solo",
		Addresses:    []string{"127.0.0.1:7050"},
		BatchTimeout: 2 * time.Second,
		BatchSize: BatchSize{
			MaxMessageCount:   10,
			AbsoluteMaxBytes:  10 * 1024 * 1024,
			PreferredMaxBytes: 512 * 1024,
		},
		Kafka: Kafka{
			Brokers: []string{"127.0.0.1:9092"},
		},
	},
}
// Load returns the orderer/application config combination that corresponds to a given profile.
func ConfigLoad(profile string) *Profile { //WAS:Load(
	config := viper.New()
	InitViper(config, "configtx") //WAS:cf.InitViper(config, configName) //SOURCE:cf.InitViper

	// For environment variables
	config.SetEnvPrefix(Prefix)
	config.AutomaticEnv()
	// This replacer allows substitution within the particular profile without having to fully qualify the name
	replacer := strings.NewReplacer(strings.ToUpper(fmt.Sprintf("profiles.%s.", profile)), "", ".", "_")
	config.SetEnvKeyReplacer(replacer)

	err := config.ReadInConfig()
	if err != nil {
		logger.Panic("Error reading configuration: ", err)
	}
	logger.Debugf("Using config file: %s", config.ConfigFileUsed())

	var uconf TopLevel
	err = EnhancedExactUnmarshal(config, &uconf) //SOURCE:viperutil.EnhancedExactUnmarshal
	if err != nil {
		logger.Panic("Error unmarshaling config into struct: ", err)
	}

	result, ok := uconf.Profiles[profile]
	if !ok {
		logger.Panic("Could not find profile: ", profile)
	}

	result.completeInitialization(filepath.Dir(config.ConfigFileUsed()))

	logger.Infof("Loaded configuration: %s", config.ConfigFileUsed())

	return result
}
func (p *Profile) completeInitialization(configDir string) {
	if p.Orderer != nil {
		for _, org := range p.Orderer.Organizations {
			if org.AdminPrincipal == "" {
				org.AdminPrincipal = AdminRoleAdminPrincipal
			}
			translatePaths(configDir, org)
		}
	}

	if p.Application != nil {
		for _, org := range p.Application.Organizations {
			if org.AdminPrincipal == "" {
				org.AdminPrincipal = AdminRoleAdminPrincipal
			}
			translatePaths(configDir, org)
		}
	}

	if p.Consortiums != nil {
		for _, consortium := range p.Consortiums {
			for _, org := range consortium.Organizations {
				if org.AdminPrincipal == "" {
					org.AdminPrincipal = AdminRoleAdminPrincipal
				}
				translatePaths(configDir, org)
			}
		}
	}

	// Some profiles will not define orderer parameters
	if p.Orderer == nil {
		return
	}

	for {
		switch {
		case p.Orderer.OrdererType == "":
			logger.Infof("Orderer.OrdererType unset, setting to %s", genesisDefaults.Orderer.OrdererType)
			p.Orderer.OrdererType = genesisDefaults.Orderer.OrdererType
		case p.Orderer.Addresses == nil:
			logger.Infof("Orderer.Addresses unset, setting to %s", genesisDefaults.Orderer.Addresses)
			p.Orderer.Addresses = genesisDefaults.Orderer.Addresses
		case p.Orderer.BatchTimeout == 0:
			logger.Infof("Orderer.BatchTimeout unset, setting to %s", genesisDefaults.Orderer.BatchTimeout)
			p.Orderer.BatchTimeout = genesisDefaults.Orderer.BatchTimeout
		case p.Orderer.BatchSize.MaxMessageCount == 0:
			logger.Infof("Orderer.BatchSize.MaxMessageCount unset, setting to %s", genesisDefaults.Orderer.BatchSize.MaxMessageCount)
			p.Orderer.BatchSize.MaxMessageCount = genesisDefaults.Orderer.BatchSize.MaxMessageCount
		case p.Orderer.BatchSize.AbsoluteMaxBytes == 0:
			logger.Infof("Orderer.BatchSize.AbsoluteMaxBytes unset, setting to %s", genesisDefaults.Orderer.BatchSize.AbsoluteMaxBytes)
			p.Orderer.BatchSize.AbsoluteMaxBytes = genesisDefaults.Orderer.BatchSize.AbsoluteMaxBytes
		case p.Orderer.BatchSize.PreferredMaxBytes == 0:
			logger.Infof("Orderer.BatchSize.PreferredMaxBytes unset, setting to %s", genesisDefaults.Orderer.BatchSize.PreferredMaxBytes)
			p.Orderer.BatchSize.PreferredMaxBytes = genesisDefaults.Orderer.BatchSize.PreferredMaxBytes
		case p.Orderer.Kafka.Brokers == nil:
			logger.Infof("Orderer.Kafka.Brokers unset, setting to %v", genesisDefaults.Orderer.Kafka.Brokers)
			p.Orderer.Kafka.Brokers = genesisDefaults.Orderer.Kafka.Brokers
		default:
			return
		}
	}
}
func translatePaths(configDir string, org *Organization) {
	TranslatePathInPlace(configDir, &org.MSPDir)  //SOURCE:cf.TranslatePathInPlace
}

/*** fabric/protos/common/policies.pb.go ***/
type Policy_PolicyType int32
const (
	Policy_UNKNOWN       Policy_PolicyType = 0
	Policy_SIGNATURE     Policy_PolicyType = 1
	Policy_MSP           Policy_PolicyType = 2
	Policy_IMPLICIT_META Policy_PolicyType = 3
)
var Policy_PolicyType_name = map[int32]string{
	0: "UNKNOWN",
	1: "SIGNATURE",
	2: "MSP",
	3: "IMPLICIT_META",
}
var Policy_PolicyType_value = map[string]int32{
	"UNKNOWN":       0,
	"SIGNATURE":     1,
	"MSP":           2,
	"IMPLICIT_META": 3,
}
type ImplicitMetaPolicy_Rule int32
const (
	ImplicitMetaPolicy_ANY      ImplicitMetaPolicy_Rule = 0
	ImplicitMetaPolicy_ALL      ImplicitMetaPolicy_Rule = 1
	ImplicitMetaPolicy_MAJORITY ImplicitMetaPolicy_Rule = 2
)
// Policy expresses a policy which the orderer can evaluate, because there has been some desire expressed to support
// multiple policy engines, this is typed as a oneof for now
type Policy struct {
	Type  int32  `protobuf:"varint,1,opt,name=type" json:"type,omitempty"`
	Value []byte `protobuf:"bytes,2,opt,name=value,proto3" json:"value,omitempty"`
}
func (m *Policy) Reset()                    { *m = Policy{} }
func (m *Policy) String() string            { return proto.CompactTextString(m) }
func (*Policy) ProtoMessage()               {}
func (*Policy) Descriptor() ([]byte, []int) { return fileDescriptor4, []int{0} }
func (m *Policy) GetType() int32 {
	if m != nil {
		return m.Type
	}
	return 0
}
func (m *Policy) GetValue() []byte {
	if m != nil {
		return m.Value
	}
	return nil
}
// SignaturePolicyEnvelope wraps a SignaturePolicy and includes a version for future enhancements
type SignaturePolicyEnvelope struct {
	Version    int32                   `protobuf:"varint,1,opt,name=version" json:"version,omitempty"`
	Rule       *SignaturePolicy        `protobuf:"bytes,2,opt,name=rule" json:"rule,omitempty"`
	Identities []*MSPPrincipal `protobuf:"bytes,3,rep,name=identities" json:"identities,omitempty"` //SOURCE:common1.MSPPrincipal
}
func (m *SignaturePolicyEnvelope) Reset()                    { *m = SignaturePolicyEnvelope{} }
func (m *SignaturePolicyEnvelope) String() string            { return proto.CompactTextString(m) }
func (*SignaturePolicyEnvelope) ProtoMessage()               {}
func (*SignaturePolicyEnvelope) Descriptor() ([]byte, []int) { return fileDescriptor4, []int{1} }
func (m *SignaturePolicyEnvelope) GetVersion() int32 {
	if m != nil {
		return m.Version
	}
	return 0
}
func (m *SignaturePolicyEnvelope) GetRule() *SignaturePolicy {
	if m != nil {
		return m.Rule
	}
	return nil
}
func (m *SignaturePolicyEnvelope) GetIdentities() []*MSPPrincipal { //SOURCE:common1.MSPPrincipal
	if m != nil {
		return m.Identities
	}
	return nil
}
// SignaturePolicy is a recursive message structure which defines a featherweight DSL for describing
// policies which are more complicated than 'exactly this signature'.  The NOutOf operator is sufficent
// to express AND as well as OR, as well as of course N out of the following M policies
// SignedBy implies that the signature is from a valid certificate which is signed by the trusted
// authority specified in the bytes.  This will be the certificate itself for a self-signed certificate
// and will be the CA for more traditional certificates
type SignaturePolicy struct {
	// Types that are valid to be assigned to Type:
	//	*SignaturePolicy_SignedBy
	//	*SignaturePolicy_NOutOf_
	Type isSignaturePolicy_Type `protobuf_oneof:"Type"`
}
func (m *SignaturePolicy) Reset()                    { *m = SignaturePolicy{} }
func (m *SignaturePolicy) String() string            { return proto.CompactTextString(m) }
func (*SignaturePolicy) ProtoMessage()               {}
func (*SignaturePolicy) Descriptor() ([]byte, []int) { return fileDescriptor4, []int{2} }
type isSignaturePolicy_Type interface {
	isSignaturePolicy_Type()
}
type SignaturePolicy_SignedBy struct {
	SignedBy int32 `protobuf:"varint,1,opt,name=signed_by,json=signedBy,oneof"`
}
type SignaturePolicy_NOutOf_ struct {
	NOutOf *SignaturePolicy_NOutOf `protobuf:"bytes,2,opt,name=n_out_of,json=nOutOf,oneof"`
}
func (*SignaturePolicy_SignedBy) isSignaturePolicy_Type() {}
func (*SignaturePolicy_NOutOf_) isSignaturePolicy_Type()  {}
func (m *SignaturePolicy) GetType() isSignaturePolicy_Type {
	if m != nil {
		return m.Type
	}
	return nil
}
func (m *SignaturePolicy) GetSignedBy() int32 {
	if x, ok := m.GetType().(*SignaturePolicy_SignedBy); ok {
		return x.SignedBy
	}
	return 0
}
func (m *SignaturePolicy) GetNOutOf() *SignaturePolicy_NOutOf {
	if x, ok := m.GetType().(*SignaturePolicy_NOutOf_); ok {
		return x.NOutOf
	}
	return nil
}
type SignaturePolicy_NOutOf struct {
	N     int32              `protobuf:"varint,1,opt,name=n" json:"n,omitempty"`
	Rules []*SignaturePolicy `protobuf:"bytes,2,rep,name=rules" json:"rules,omitempty"`
}
func (m *SignaturePolicy_NOutOf) Reset()                    { *m = SignaturePolicy_NOutOf{} }
func (m *SignaturePolicy_NOutOf) String() string            { return proto.CompactTextString(m) }
func (*SignaturePolicy_NOutOf) ProtoMessage()               {}
func (*SignaturePolicy_NOutOf) Descriptor() ([]byte, []int) { return fileDescriptor4, []int{2, 0} }
func (m *SignaturePolicy_NOutOf) GetN() int32 {
	if m != nil {
		return m.N
	}
	return 0
}
func (m *SignaturePolicy_NOutOf) GetRules() []*SignaturePolicy {
	if m != nil {
		return m.Rules
	}
	return nil
}
// ImplicitMetaPolicy is a policy type which depends on the hierarchical nature of the configuration
// It is implicit because the rule is generate implicitly based on the number of sub policies
// It is meta because it depends only on the result of other policies
// When evaluated, this policy iterates over all immediate child sub-groups, retrieves the policy
// of name sub_policy, evaluates the collection and applies the rule.
// For example, with 4 sub-groups, and a policy name of "foo", ImplicitMetaPolicy retrieves
// each sub-group, retrieves policy "foo" for each subgroup, evaluates it, and, in the case of ANY
// 1 satisfied is sufficient, ALL would require 4 signatures, and MAJORITY would require 3 signatures.
type ImplicitMetaPolicy struct {
	SubPolicy string                  `protobuf:"bytes,1,opt,name=sub_policy,json=subPolicy" json:"sub_policy,omitempty"`
	Rule      ImplicitMetaPolicy_Rule `protobuf:"varint,2,opt,name=rule,enum=common.ImplicitMetaPolicy_Rule" json:"rule,omitempty"`
}
func (m *ImplicitMetaPolicy) Reset()                    { *m = ImplicitMetaPolicy{} }
func (m *ImplicitMetaPolicy) String() string            { return proto.CompactTextString(m) }
func (*ImplicitMetaPolicy) ProtoMessage()               {}
func (*ImplicitMetaPolicy) Descriptor() ([]byte, []int) { return fileDescriptor4, []int{3} }
func (m *ImplicitMetaPolicy) GetSubPolicy() string {
	if m != nil {
		return m.SubPolicy
	}
	return ""
}
func (m *ImplicitMetaPolicy) GetRule() ImplicitMetaPolicy_Rule {
	if m != nil {
		return m.Rule
	}
	return ImplicitMetaPolicy_ANY
}
var fileDescriptor4 = []byte{
	// 480 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x09, 0x6e, 0x88, 0x02, 0xff, 0x74, 0x52, 0xdf, 0x8b, 0xda, 0x40,
	0x10, 0x76, 0xfd, 0x11, 0x75, 0xf4, 0xda, 0x74, 0xb9, 0xa2, 0x1c, 0xb4, 0x95, 0x50, 0x8a, 0x70,
	0x34, 0x01, 0xaf, 0x4f, 0x7d, 0xd3, 0x56, 0x7a, 0x69, 0x4d, 0x94, 0xd5, 0xa3, 0x5c, 0x5f, 0x82,
	0xd1, 0xd5, 0x5b, 0x88, 0xbb, 0x4b, 0x76, 0x23, 0xf5, 0xbf, 0xe8, 0x53, 0xff, 0x99, 0xfe, 0x73,
	0x25, 0x59, 0x2d, 0x72, 0xe5, 0xde, 0xe6, 0x9b, 0xfd, 0x66, 0xf6, 0xfb, 0x66, 0x06, 0x5e, 0xae,
	0xc4, 0x6e, 0x27, 0xb8, 0x27, 0x45, 0xc2, 0x56, 0x8c, 0x2a, 0x57, 0xa6, 0x42, 0x0b, 0x6c, 0x99,
	0xf4, 0x55, 0x67, 0xa7, 0xa4, 0xb7, 0x53, 0x32, 0x92, 0x29, 0xe3, 0x2b, 0x26, 0x97, 0x89, 0x21,
	0x38, 0x3f, 0xc1, 0x9a, 0xe5, 0x25, 0x07, 0x8c, 0xa1, 0xaa, 0x0f, 0x92, 0x76, 0x51, 0x0f, 0xf5,
	0x6b, 0xa4, 0x88, 0xf1, 0x25, 0xd4, 0xf6, 0xcb, 0x24, 0xa3, 0xdd, 0x72, 0x0f, 0xf5, 0xdb, 0xc4,
	0x00, 0xe7, 0x33, 0x80, 0xa9, 0x59, 0xe4, 0x9c, 0x16, 0xd4, 0xef, 0xc2, 0x6f, 0xe1, 0xf4, 0x7b,
	0x68, 0x97, 0xf0, 0x05, 0x34, 0xe7, 0xfe, 0x97, 0x70, 0xb8, 0xb8, 0x23, 0x63, 0x1b, 0xe1, 0x3a,
	0x54, 0x82, 0xf9, 0xcc, 0x2e, 0xe3, 0x17, 0x70, 0xe1, 0x07, 0xb3, 0x89, 0xff, 0xc9, 0x5f, 0x44,
	0xc1, 0x78, 0x31, 0xb4, 0x2b, 0xce, 0x6f, 0x04, 0x9d, 0x39, 0xdb, 0xf2, 0xa5, 0xce, 0x52, 0x6a,
	0xfa, 0x8d, 0xf9, 0x9e, 0x26, 0x42, 0x52, 0xdc, 0x85, 0xfa, 0x9e, 0xa6, 0x8a, 0x09, 0x7e, 0x94,
	0x73, 0x82, 0xf8, 0x1a, 0xaa, 0x69, 0x96, 0x18, 0x41, 0xad, 0x41, 0xc7, 0x35, 0xfe, 0xdc, 0x47,
	0x8d, 0x48, 0x41, 0xc2, 0x1f, 0x00, 0xd8, 0x9a, 0x72, 0xcd, 0x34, 0xa3, 0xaa, 0x5b, 0xe9, 0x55,
	0xfa, 0xad, 0xc1, 0xe5, 0xa9, 0x24, 0x98, 0xcf, 0x66, 0xa7, 0x61, 0x90, 0x33, 0x9e, 0xf3, 0x07,
	0xc1, 0xf3, 0x47, 0xfd, 0xf0, 0x2b, 0x68, 0x2a, 0xb6, 0xe5, 0x74, 0x1d, 0xc5, 0x07, 0x23, 0xe9,
	0xb6, 0x44, 0x1a, 0x26, 0x35, 0x3a, 0xe0, 0x8f, 0xd0, 0xe0, 0x91, 0xc8, 0x74, 0x24, 0x36, 0x47,
	0x65, 0xaf, 0x9f, 0x50, 0xe6, 0x86, 0xd3, 0x4c, 0x4f, 0x37, 0xb7, 0x25, 0x62, 0xf1, 0x22, 0xba,
	0x1a, 0x83, 0x65, 0x72, 0xb8, 0x0d, 0xe8, 0xe4, 0x17, 0x71, 0xfc, 0x1e, 0x6a, 0xb9, 0x09, 0xd5,
	0x2d, 0x17, 0xba, 0x9f, 0xb4, 0x6a, 0x58, 0x23, 0x0b, 0xaa, 0xf9, 0x3a, 0x9c, 0x5f, 0x08, 0xb0,
	0xbf, 0x93, 0xf9, 0x15, 0xe8, 0x80, 0xea, 0xe5, 0x3f, 0x03, 0xa0, 0xb2, 0x38, 0x2a, 0xce, 0xc3,
	0x38, 0x68, 0x92, 0xa6, 0xca, 0xe2, 0xe3, 0xf3, 0xcd, 0xd9, 0x58, 0x9f, 0x0d, 0xde, 0x9c, 0xfe,
	0xfa, 0xbf, 0x91, 0x4b, 0xb2, 0x84, 0x9a, 0xf1, 0x3a, 0xef, 0xa0, 0x9a, 0xa3, 0x7c, 0xcb, 0xc3,
	0xf0, 0xde, 0x2e, 0x15, 0xc1, 0x64, 0x62, 0x23, 0xdc, 0x86, 0x46, 0x30, 0xfc, 0x3a, 0x25, 0xfe,
	0xe2, 0xde, 0x2e, 0x8f, 0xe6, 0xf0, 0x56, 0xa4, 0x5b, 0xf7, 0xe1, 0x20, 0x69, 0x9a, 0xd0, 0xf5,
	0x96, 0xa6, 0xee, 0x66, 0x19, 0xa7, 0x6c, 0x65, 0x6e, 0x50, 0x1d, 0x7f, 0xfb, 0x71, 0xbd, 0x65,
	0xfa, 0x21, 0x8b, 0x73, 0xe8, 0x9d, 0x91, 0x3d, 0x43, 0xf6, 0x0c, 0xd9, 0x33, 0xe4, 0xd8, 0x2a,
	0xe0, 0xcd, 0xdf, 0x00, 0x00, 0x00, 0xff, 0xff, 0x34, 0xab, 0x8a, 0xb5, 0xf9, 0x02, 0x00, 0x00,
}

/*** fabric/protos/common/configtx.pb.go ***/
// ConfigEnvelope is designed to contain _all_ configuration for a chain with no dependency
// on previous configuration transactions.
//
// It is generated with the following scheme:
//   1. Retrieve the existing configuration
//   2. Note the config properties (ConfigValue, ConfigPolicy, ConfigGroup) to be modified
//   3. Add any intermediate ConfigGroups to the ConfigUpdate.read_set (sparsely)
//   4. Add any additional desired dependencies to ConfigUpdate.read_set (sparsely)
//   5. Modify the config properties, incrementing each version by 1, set them in the ConfigUpdate.write_set
//      Note: any element not modified but specified should already be in the read_set, so may be specified sparsely
//   6. Create ConfigUpdate message and marshal it into ConfigUpdateEnvelope.update and encode the required signatures
//     a) Each signature is of type ConfigSignature
//     b) The ConfigSignature signature is over the concatenation of signature_header and the ConfigUpdate bytes (which includes a ChainHeader)
//   5. Submit new Config for ordering in Envelope signed by submitter
//     a) The Envelope Payload has data set to the marshaled ConfigEnvelope
//     b) The Envelope Payload has a header of type Header.Type.CONFIG_UPDATE
//
// The configuration manager will verify:
//   1. All items in the read_set exist at the read versions
//   2. All items in the write_set at a different version than, or not in, the read_set have been appropriately signed according to their mod_policy
//   3. The new configuration satisfies the ConfigSchema
type ConfigEnvelope struct {
	Config     *Config   `protobuf:"bytes,1,opt,name=config" json:"config,omitempty"`
	LastUpdate *Envelope `protobuf:"bytes,2,opt,name=last_update,json=lastUpdate" json:"last_update,omitempty"`
}
func (m *ConfigEnvelope) Reset()                    { *m = ConfigEnvelope{} }
func (m *ConfigEnvelope) String() string            { return proto.CompactTextString(m) }
func (*ConfigEnvelope) ProtoMessage()               {}
func (*ConfigEnvelope) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{0} }
func (m *ConfigEnvelope) GetConfig() *Config {
	if m != nil {
		return m.Config
	}
	return nil
}
func (m *ConfigEnvelope) GetLastUpdate() *Envelope {
	if m != nil {
		return m.LastUpdate
	}
	return nil
}
// Config represents the config for a particular channel
type Config struct {
	Sequence     uint64       `protobuf:"varint,1,opt,name=sequence" json:"sequence,omitempty"`
	ChannelGroup *ConfigGroup `protobuf:"bytes,2,opt,name=channel_group,json=channelGroup" json:"channel_group,omitempty"`
}
func (m *Config) Reset()                    { *m = Config{} }
func (m *Config) String() string            { return proto.CompactTextString(m) }
func (*Config) ProtoMessage()               {}
func (*Config) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{4} }
func (m *Config) GetSequence() uint64 {
	if m != nil {
		return m.Sequence
	}
	return 0
}
func (m *Config) GetChannelGroup() *ConfigGroup {
	if m != nil {
		return m.ChannelGroup
	}
	return nil
}
// ConfigUpdate is used to submit a subset of config and to have the orderer apply to Config
// it is always submitted inside a ConfigUpdateEnvelope which allows the addition of signatures
// resulting in a new total configuration.  The update is applied as follows:
// 1. The versions from all of the elements in the read_set is verified against the versions in the existing config.
//    If there is a mismatch in the read versions, then the config update fails and is rejected.
// 2. Any elements in the write_set with the same version as the read_set are ignored.
// 3. The corresponding mod_policy for every remaining element in the write_set is collected.
// 4. Each policy is checked against the signatures from the ConfigUpdateEnvelope, any failing to verify are rejected
// 5. The write_set is applied to the Config and the ConfigGroupSchema verifies that the updates were legal
type ConfigUpdate struct {
	ChannelId string       `protobuf:"bytes,1,opt,name=channel_id,json=channelId" json:"channel_id,omitempty"`
	ReadSet   *ConfigGroup `protobuf:"bytes,2,opt,name=read_set,json=readSet" json:"read_set,omitempty"`
	WriteSet  *ConfigGroup `protobuf:"bytes,3,opt,name=write_set,json=writeSet" json:"write_set,omitempty"`
}
func (m *ConfigUpdate) Reset()                    { *m = ConfigUpdate{} }
func (m *ConfigUpdate) String() string            { return proto.CompactTextString(m) }
func (*ConfigUpdate) ProtoMessage()               {}
func (*ConfigUpdate) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{6} }
func (m *ConfigUpdate) GetChannelId() string {
	if m != nil {
		return m.ChannelId
	}
	return ""
}
func (m *ConfigUpdate) GetReadSet() *ConfigGroup {
	if m != nil {
		return m.ReadSet
	}
	return nil
}
func (m *ConfigUpdate) GetWriteSet() *ConfigGroup {
	if m != nil {
		return m.WriteSet
	}
	return nil
}
type ConfigUpdateEnvelope struct {
	ConfigUpdate []byte             `protobuf:"bytes,1,opt,name=config_update,json=configUpdate,proto3" json:"config_update,omitempty"`
	Signatures   []*ConfigSignature `protobuf:"bytes,2,rep,name=signatures" json:"signatures,omitempty"`
}
func (m *ConfigUpdateEnvelope) Reset()                    { *m = ConfigUpdateEnvelope{} }
func (m *ConfigUpdateEnvelope) String() string            { return proto.CompactTextString(m) }
func (*ConfigUpdateEnvelope) ProtoMessage()               {}
func (*ConfigUpdateEnvelope) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{5} }
func (m *ConfigUpdateEnvelope) GetConfigUpdate() []byte {
	if m != nil {
		return m.ConfigUpdate
	}
	return nil
}
func (m *ConfigUpdateEnvelope) GetSignatures() []*ConfigSignature {
	if m != nil {
		return m.Signatures
	}
	return nil
}
// ConfigGroup is the hierarchical data structure for holding config
type ConfigGroup struct {
	Version   uint64                   `protobuf:"varint,1,opt,name=version" json:"version,omitempty"`
	Groups    map[string]*ConfigGroup  `protobuf:"bytes,2,rep,name=groups" json:"groups,omitempty" protobuf_key:"bytes,1,opt,name=key" protobuf_val:"bytes,2,opt,name=value"`
	Values    map[string]*ConfigValue  `protobuf:"bytes,3,rep,name=values" json:"values,omitempty" protobuf_key:"bytes,1,opt,name=key" protobuf_val:"bytes,2,opt,name=value"`
	Policies  map[string]*ConfigPolicy `protobuf:"bytes,4,rep,name=policies" json:"policies,omitempty" protobuf_key:"bytes,1,opt,name=key" protobuf_val:"bytes,2,opt,name=value"`
	ModPolicy string                   `protobuf:"bytes,5,opt,name=mod_policy,json=modPolicy" json:"mod_policy,omitempty"`
}
func (m *ConfigGroup) Reset()                    { *m = ConfigGroup{} }
func (m *ConfigGroup) String() string            { return proto.CompactTextString(m) }
func (*ConfigGroup) ProtoMessage()               {}
func (*ConfigGroup) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{7} }
func (m *ConfigGroup) GetVersion() uint64 {
	if m != nil {
		return m.Version
	}
	return 0
}
func (m *ConfigGroup) GetGroups() map[string]*ConfigGroup {
	if m != nil {
		return m.Groups
	}
	return nil
}
func (m *ConfigGroup) GetValues() map[string]*ConfigValue {
	if m != nil {
		return m.Values
	}
	return nil
}
func (m *ConfigGroup) GetPolicies() map[string]*ConfigPolicy {
	if m != nil {
		return m.Policies
	}
	return nil
}
// ConfigValue represents an individual piece of config data
type ConfigValue struct {
	Version   uint64 `protobuf:"varint,1,opt,name=version" json:"version,omitempty"`
	Value     []byte `protobuf:"bytes,2,opt,name=value,proto3" json:"value,omitempty"`
	ModPolicy string `protobuf:"bytes,3,opt,name=mod_policy,json=modPolicy" json:"mod_policy,omitempty"`
}
func (m *ConfigValue) Reset()                    { *m = ConfigValue{} }
func (m *ConfigValue) String() string            { return proto.CompactTextString(m) }
func (*ConfigValue) ProtoMessage()               {}
func (*ConfigValue) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{8} }
func (m *ConfigValue) GetVersion() uint64 {
	if m != nil {
		return m.Version
	}
	return 0
}
func (m *ConfigValue) GetValue() []byte {
	if m != nil {
		return m.Value
	}
	return nil
}
func (m *ConfigValue) GetModPolicy() string {
	if m != nil {
		return m.ModPolicy
	}
	return ""
}
type ConfigPolicy struct {
	Version   uint64  `protobuf:"varint,1,opt,name=version" json:"version,omitempty"`
	Policy    *Policy `protobuf:"bytes,2,opt,name=policy" json:"policy,omitempty"`
	ModPolicy string  `protobuf:"bytes,3,opt,name=mod_policy,json=modPolicy" json:"mod_policy,omitempty"`
}
func (m *ConfigPolicy) Reset()                    { *m = ConfigPolicy{} }
func (m *ConfigPolicy) String() string            { return proto.CompactTextString(m) }
func (*ConfigPolicy) ProtoMessage()               {}
func (*ConfigPolicy) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{9} }
func (m *ConfigPolicy) GetVersion() uint64 {
	if m != nil {
		return m.Version
	}
	return 0
}
func (m *ConfigPolicy) GetPolicy() *Policy {
	if m != nil {
		return m.Policy
	}
	return nil
}
func (m *ConfigPolicy) GetModPolicy() string {
	if m != nil {
		return m.ModPolicy
	}
	return ""
}
type ConfigSignature struct {
	SignatureHeader []byte `protobuf:"bytes,1,opt,name=signature_header,json=signatureHeader,proto3" json:"signature_header,omitempty"`
	Signature       []byte `protobuf:"bytes,2,opt,name=signature,proto3" json:"signature,omitempty"`
}
func (m *ConfigSignature) Reset()                    { *m = ConfigSignature{} }
func (m *ConfigSignature) String() string            { return proto.CompactTextString(m) }
func (*ConfigSignature) ProtoMessage()               {}
func (*ConfigSignature) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{10} }
func (m *ConfigSignature) GetSignatureHeader() []byte {
	if m != nil {
		return m.SignatureHeader
	}
	return nil
}
func (m *ConfigSignature) GetSignature() []byte {
	if m != nil {
		return m.Signature
	}
	return nil
}
var fileDescriptor1 = []byte{
	// 674 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x09, 0x6e, 0x88, 0x02, 0xff, 0x94, 0x55, 0xdb, 0x6e, 0xd3, 0x40,
	0x10, 0x55, 0xe2, 0xd6, 0x4d, 0x26, 0xe9, 0x85, 0x6d, 0x10, 0xc6, 0x02, 0x51, 0x0c, 0x94, 0x16,
	0x24, 0xa7, 0x94, 0x87, 0x56, 0x48, 0x7d, 0xa1, 0xaa, 0x80, 0x97, 0x0a, 0x1c, 0x2e, 0x52, 0x85,
	0x88, 0x5c, 0x7b, 0xeb, 0x58, 0x75, 0xbc, 0x66, 0xbd, 0x2e, 0xe4, 0x2b, 0xf8, 0x40, 0xfe, 0x80,
	0xaf, 0x40, 0xde, 0x5d, 0x9b, 0x75, 0xe2, 0x24, 0xe2, 0x29, 0x99, 0x99, 0x73, 0xce, 0xec, 0xce,
	0xce, 0x91, 0xe1, 0xb6, 0x47, 0xc6, 0x63, 0x12, 0xf7, 0x3d, 0x12, 0x5f, 0x85, 0x01, 0xfb, 0x69,
	0x27, 0x94, 0x30, 0x82, 0x74, 0x91, 0x36, 0xb7, 0xcb, 0x72, 0xfe, 0x23, 0x8a, 0x66, 0xc1, 0x49,
	0x48, 0x14, 0x7a, 0x21, 0x4e, 0x45, 0xda, 0xba, 0x86, 0x8d, 0x53, 0xae, 0x72, 0x16, 0xdf, 0xe0,
	0x88, 0x24, 0x18, 0xed, 0x82, 0x2e, 0x74, 0x8d, 0xc6, 0x4e, 0x63, 0xaf, 0x73, 0xb8, 0x61, 0x4b,
	0x1d, 0x81, 0x73, 0x64, 0x15, 0xbd, 0x80, 0x4e, 0xe4, 0xa6, 0x6c, 0x98, 0x25, 0xbe, 0xcb, 0xb0,
	0xd1, 0xe4, 0xe0, 0xad, 0x02, 0x5c, 0xc8, 0x39, 0x90, 0x83, 0x3e, 0x71, 0x8c, 0xf5, 0x5b, 0x83,
	0x5b, 0x42, 0xe5, 0x0d, 0x25, 0x59, 0x32, 0xf0, 0x46, 0x78, 0xec, 0xa2, 0x13, 0xd0, 0x83, 0x3c,
	0x4c, 0x8d, 0xc6, 0x8e, 0xb6, 0xd7, 0x39, 0x7c, 0x52, 0x6d, 0xa8, 0x40, 0x6d, 0xfe, 0x3f, 0x3d,
	0x8b, 0x19, 0x9d, 0x38, 0x92, 0x94, 0xd3, 0x6f, 0xdc, 0x28, 0xc3, 0xa9, 0xd1, 0x5c, 0x46, 0xff,
	0xcc, 0x71, 0x92, 0x2e, 0x48, 0xe8, 0x14, 0x5a, 0xc5, 0x48, 0x0c, 0x8d, 0x0b, 0x3c, 0x9d, 0x2f,
	0xf0, 0x5e, 0x22, 0x85, 0x44, 0x49, 0x34, 0x3f, 0x42, 0x47, 0x39, 0x1a, 0xda, 0x02, 0xed, 0x1a,
	0x4f, 0xf8, 0xfc, 0xda, 0x4e, 0xfe, 0x17, 0xf5, 0x61, 0x95, 0xf7, 0x93, 0x63, 0xba, 0x3b, 0xb7,
	0x85, 0x23, 0x70, 0xaf, 0x9a, 0xc7, 0x8d, 0x5c, 0x55, 0x39, 0xf1, 0x7f, 0xab, 0x72, 0xee, 0xac,
	0xea, 0x17, 0x58, 0xaf, 0x5c, 0xa3, 0x46, 0xf7, 0xa0, 0xaa, 0x6b, 0x56, 0x75, 0x39, 0x7b, 0x32,
	0x23, 0x6c, 0x6d, 0x17, 0x8f, 0xab, 0x34, 0xb6, 0x7a, 0x80, 0x66, 0x59, 0xd6, 0x37, 0xd0, 0x45,
	0x16, 0x99, 0xd0, 0x4a, 0xf1, 0xf7, 0x0c, 0xc7, 0x1e, 0xe6, 0x27, 0x58, 0x71, 0xca, 0x18, 0x1d,
	0xc3, 0xba, 0x37, 0x72, 0xe3, 0x18, 0x47, 0x43, 0xfe, 0xd6, 0xf2, 0x38, 0xdb, 0x35, 0xc3, 0x73,
	0xba, 0x12, 0xc9, 0x23, 0x8b, 0x41, 0x4f, 0x14, 0xc5, 0xe2, 0x95, 0xbb, 0xfd, 0x08, 0xd6, 0xc5,
	0xf6, 0x16, 0x5b, 0x9b, 0xb7, 0xec, 0x3a, 0x5d, 0x4f, 0x01, 0xa3, 0x23, 0x80, 0x34, 0x0c, 0x62,
	0x97, 0x65, 0xb4, 0x5c, 0xaa, 0x3b, 0xd5, 0x9e, 0x83, 0xa2, 0xee, 0x28, 0x50, 0xeb, 0x57, 0x03,
	0xba, 0x6a, 0x5b, 0x74, 0x1f, 0xa0, 0xb8, 0x40, 0xe8, 0xcb, 0x01, 0xb7, 0x65, 0xe6, 0x9d, 0x8f,
	0x6c, 0x68, 0x51, 0xec, 0xfa, 0xc3, 0x14, 0xb3, 0x45, 0x57, 0x5b, 0xcb, 0x41, 0x03, 0xcc, 0xd0,
	0x01, 0xb4, 0x7f, 0xd0, 0x90, 0x61, 0x4e, 0xd0, 0xe6, 0x13, 0x5a, 0x1c, 0x35, 0xc0, 0xcc, 0xfa,
	0xa3, 0x41, 0x47, 0xa9, 0x20, 0x03, 0xd6, 0x6e, 0x30, 0x4d, 0x43, 0x12, 0xcb, 0x61, 0x17, 0x21,
	0x3a, 0x2a, 0x4d, 0x28, 0x2e, 0xfc, 0xa0, 0x46, 0xb8, 0xd6, 0x7e, 0x47, 0xa5, 0xfd, 0xb4, 0xf9,
	0xc4, 0x3a, 0xe3, 0x9d, 0x28, 0xc6, 0x5b, 0xe1, 0xd4, 0x87, 0x75, 0xd4, 0x39, 0x96, 0xcb, 0x67,
	0x3b, 0x26, 0xfe, 0x90, 0xc7, 0x13, 0x63, 0x55, 0xcc, 0x76, 0x4c, 0x7c, 0xb1, 0x67, 0xe6, 0xf9,
	0x32, 0x47, 0xee, 0x57, 0x77, 0xbc, 0x76, 0x90, 0x8a, 0x6b, 0xce, 0x97, 0x79, 0x71, 0xb1, 0x1e,
	0xe7, 0xaa, 0x7a, 0x1f, 0x96, 0xbb, 0xf0, 0x59, 0x55, 0xb1, 0x57, 0xe7, 0x42, 0xd5, 0x7f, 0x5f,
	0x8b, 0xb7, 0xe6, 0xcd, 0x16, 0xbc, 0x75, 0x4f, 0x15, 0xee, 0x4a, 0x89, 0xa9, 0x81, 0x6a, 0x53,
	0x03, 0xb5, 0x48, 0xb1, 0xdb, 0x22, 0x5e, 0x20, 0xbf, 0x0b, 0xba, 0x14, 0x69, 0x56, 0x3f, 0x20,
	0xf2, 0xc8, 0xb2, 0xba, 0xac, 0xe1, 0x05, 0x6c, 0x4e, 0x99, 0x0d, 0xed, 0xc3, 0x56, 0x69, 0xb7,
	0xe1, 0x08, 0xbb, 0x3e, 0xa6, 0xd2, 0xc1, 0x9b, 0x65, 0xfe, 0x2d, 0x4f, 0xa3, 0x7b, 0xd0, 0x2e,
	0x53, 0xf2, 0x9e, 0xff, 0x12, 0xaf, 0x07, 0xf0, 0x98, 0xd0, 0xc0, 0x1e, 0x4d, 0x12, 0x4c, 0x23,
	0xec, 0x07, 0x98, 0xda, 0x57, 0xee, 0x25, 0x0d, 0x3d, 0xf1, 0x55, 0x4c, 0xe5, 0x89, 0x2f, 0x9e,
	0x07, 0x21, 0x1b, 0x65, 0x97, 0x79, 0xd8, 0x57, 0xc0, 0x7d, 0x01, 0xee, 0x0b, 0xb0, 0xfc, 0xce,
	0x5e, 0xea, 0x3c, 0x7c, 0xf9, 0x37, 0x00, 0x00, 0xff, 0xff, 0x25, 0x75, 0xfb, 0xf8, 0x9e, 0x07,
	0x00, 0x00,
}

/*** fabric/protos/common/common.pb.go ***/
type HeaderType int32
const (
	HeaderType_MESSAGE              HeaderType = 0
	HeaderType_CONFIG               HeaderType = 1
	HeaderType_CONFIG_UPDATE        HeaderType = 2
	HeaderType_ENDORSER_TRANSACTION HeaderType = 3
	HeaderType_ORDERER_TRANSACTION  HeaderType = 4
	HeaderType_DELIVER_SEEK_INFO    HeaderType = 5
	HeaderType_CHAINCODE_PACKAGE    HeaderType = 6
)
var HeaderType_name = map[int32]string{
	0: "MESSAGE",
	1: "CONFIG",
	2: "CONFIG_UPDATE",
	3: "ENDORSER_TRANSACTION",
	4: "ORDERER_TRANSACTION",
	5: "DELIVER_SEEK_INFO",
	6: "CHAINCODE_PACKAGE",
}
var HeaderType_value = map[string]int32{
	"MESSAGE":              0,
	"CONFIG":               1,
	"CONFIG_UPDATE":        2,
	"ENDORSER_TRANSACTION": 3,
	"ORDERER_TRANSACTION":  4,
	"DELIVER_SEEK_INFO":    5,
	"CHAINCODE_PACKAGE":    6,
}
func (x HeaderType) String() string {
	return proto.EnumName(HeaderType_name, int32(x))
}
func (HeaderType) EnumDescriptor() ([]byte, []int) { return fileDescriptor0, []int{1} }
// This enum enlists indexes of the block metadata array
type BlockMetadataIndex int32
const (
	BlockMetadataIndex_SIGNATURES          BlockMetadataIndex = 0
	BlockMetadataIndex_LAST_CONFIG         BlockMetadataIndex = 1
	BlockMetadataIndex_TRANSACTIONS_FILTER BlockMetadataIndex = 2
	BlockMetadataIndex_ORDERER             BlockMetadataIndex = 3
)
var BlockMetadataIndex_name = map[int32]string{
	0: "SIGNATURES",
	1: "LAST_CONFIG",
	2: "TRANSACTIONS_FILTER",
	3: "ORDERER",
}
var BlockMetadataIndex_value = map[string]int32{
	"SIGNATURES":          0,
	"LAST_CONFIG":         1,
	"TRANSACTIONS_FILTER": 2,
	"ORDERER":             3,
}
func (x BlockMetadataIndex) String() string {
	return proto.EnumName(BlockMetadataIndex_name, int32(x))
}
func (BlockMetadataIndex) EnumDescriptor() ([]byte, []int) { return fileDescriptor0, []int{2} }
// LastConfig is the encoded value for the Metadata message which is encoded in the LAST_CONFIGURATION block metadata index
type LastConfig struct {
	Index uint64 `protobuf:"varint,1,opt,name=index" json:"index,omitempty"`
}
func (m *LastConfig) Reset()                    { *m = LastConfig{} }
func (m *LastConfig) String() string            { return proto.CompactTextString(m) }
func (*LastConfig) ProtoMessage()               {}
func (*LastConfig) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{0} }
func (m *LastConfig) GetIndex() uint64 {
	if m != nil {
		return m.Index
	}
	return 0
}
// Metadata is a common structure to be used to encode block metadata
type Metadata struct {
	Value      []byte               `protobuf:"bytes,1,opt,name=value,proto3" json:"value,omitempty"`
	Signatures []*MetadataSignature `protobuf:"bytes,2,rep,name=signatures" json:"signatures,omitempty"`
}
func (m *Metadata) Reset()                    { *m = Metadata{} }
func (m *Metadata) String() string            { return proto.CompactTextString(m) }
func (*Metadata) ProtoMessage()               {}
func (*Metadata) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{1} }
func (m *Metadata) GetValue() []byte {
	if m != nil {
		return m.Value
	}
	return nil
}
func (m *Metadata) GetSignatures() []*MetadataSignature {
	if m != nil {
		return m.Signatures
	}
	return nil
}
type MetadataSignature struct {
	SignatureHeader []byte `protobuf:"bytes,1,opt,name=signature_header,json=signatureHeader,proto3" json:"signature_header,omitempty"`
	Signature       []byte `protobuf:"bytes,2,opt,name=signature,proto3" json:"signature,omitempty"`
}
func (m *MetadataSignature) Reset()                    { *m = MetadataSignature{} }
func (m *MetadataSignature) String() string            { return proto.CompactTextString(m) }
func (*MetadataSignature) ProtoMessage()               {}
func (*MetadataSignature) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{2} }
func (m *MetadataSignature) GetSignatureHeader() []byte {
	if m != nil {
		return m.SignatureHeader
	}
	return nil
}
func (m *MetadataSignature) GetSignature() []byte {
	if m != nil {
		return m.Signature
	}
	return nil
}
type Header struct {
	ChannelHeader   []byte `protobuf:"bytes,1,opt,name=channel_header,json=channelHeader,proto3" json:"channel_header,omitempty"`
	SignatureHeader []byte `protobuf:"bytes,2,opt,name=signature_header,json=signatureHeader,proto3" json:"signature_header,omitempty"`
}
func (m *Header) Reset()                    { *m = Header{} }
func (m *Header) String() string            { return proto.CompactTextString(m) }
func (*Header) ProtoMessage()               {}
func (*Header) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{3} }
func (m *Header) GetChannelHeader() []byte {
	if m != nil {
		return m.ChannelHeader
	}
	return nil
}
func (m *Header) GetSignatureHeader() []byte {
	if m != nil {
		return m.SignatureHeader
	}
	return nil
}
// Header is a generic replay prevention and identity message to include in a signed payload
type ChannelHeader struct {
	Type int32 `protobuf:"varint,1,opt,name=type" json:"type,omitempty"`
	// Version indicates message protocol version
	Version int32 `protobuf:"varint,2,opt,name=version" json:"version,omitempty"`
	// Timestamp is the local time when the message was created
	// by the sender
	Timestamp *timestamp.Timestamp `protobuf:"bytes,3,opt,name=timestamp" json:"timestamp,omitempty"` //WAS:google_protobuf.Timestamp
	// Identifier of the channel this message is bound for
	ChannelId string `protobuf:"bytes,4,opt,name=channel_id,json=channelId" json:"channel_id,omitempty"`
	// An unique identifier that is used end-to-end.
	//  -  set by higher layers such as end user or SDK
	//  -  passed to the endorser (which will check for uniqueness)
	//  -  as the header is passed along unchanged, it will be
	//     be retrieved by the committer (uniqueness check here as well)
	//  -  to be stored in the ledger
	TxId string `protobuf:"bytes,5,opt,name=tx_id,json=txId" json:"tx_id,omitempty"`
	// The epoch in which this header was generated, where epoch is defined based on block height
	// Epoch in which the response has been generated. This field identifies a
	// logical window of time. A proposal response is accepted by a peer only if
	// two conditions hold:
	// 1. the epoch specified in the message is the current epoch
	// 2. this message has been only seen once during this epoch (i.e. it hasn't
	//    been replayed)
	Epoch uint64 `protobuf:"varint,6,opt,name=epoch" json:"epoch,omitempty"`
	// Extension that may be attached based on the header type
	Extension []byte `protobuf:"bytes,7,opt,name=extension,proto3" json:"extension,omitempty"`
}
func (m *ChannelHeader) Reset()                    { *m = ChannelHeader{} }
func (m *ChannelHeader) String() string            { return proto.CompactTextString(m) }
func (*ChannelHeader) ProtoMessage()               {}
func (*ChannelHeader) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{4} }
func (m *ChannelHeader) GetType() int32 {
	if m != nil {
		return m.Type
	}
	return 0
}
func (m *ChannelHeader) GetVersion() int32 {
	if m != nil {
		return m.Version
	}
	return 0
}
func (m *ChannelHeader) GetTimestamp() *timestamp.Timestamp { //WAS:google_protobuf.Timestamp
	if m != nil {
		return m.Timestamp
	}
	return nil
}
func (m *ChannelHeader) GetChannelId() string {
	if m != nil {
		return m.ChannelId
	}
	return ""
}
func (m *ChannelHeader) GetTxId() string {
	if m != nil {
		return m.TxId
	}
	return ""
}
func (m *ChannelHeader) GetEpoch() uint64 {
	if m != nil {
		return m.Epoch
	}
	return 0
}
func (m *ChannelHeader) GetExtension() []byte {
	if m != nil {
		return m.Extension
	}
	return nil
}
type SignatureHeader struct {
	// Creator of the message, specified as a certificate chain
	Creator []byte `protobuf:"bytes,1,opt,name=creator,proto3" json:"creator,omitempty"`
	// Arbitrary number that may only be used once. Can be used to detect replay attacks.
	Nonce []byte `protobuf:"bytes,2,opt,name=nonce,proto3" json:"nonce,omitempty"`
}
func (m *SignatureHeader) Reset()                    { *m = SignatureHeader{} }
func (m *SignatureHeader) String() string            { return proto.CompactTextString(m) }
func (*SignatureHeader) ProtoMessage()               {}
func (*SignatureHeader) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{5} }
func (m *SignatureHeader) GetCreator() []byte {
	if m != nil {
		return m.Creator
	}
	return nil
}
func (m *SignatureHeader) GetNonce() []byte {
	if m != nil {
		return m.Nonce
	}
	return nil
}
// Payload is the message contents (and header to allow for signing)
type Payload struct {
	// Header is included to provide identity and prevent replay
	Header *Header `protobuf:"bytes,1,opt,name=header" json:"header,omitempty"`
	// Data, the encoding of which is defined by the type in the header
	Data []byte `protobuf:"bytes,2,opt,name=data,proto3" json:"data,omitempty"`
}
func (m *Payload) Reset()                    { *m = Payload{} }
func (m *Payload) String() string            { return proto.CompactTextString(m) }
func (*Payload) ProtoMessage()               {}
func (*Payload) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{6} }
func (m *Payload) GetHeader() *Header {
	if m != nil {
		return m.Header
	}
	return nil
}
func (m *Payload) GetData() []byte {
	if m != nil {
		return m.Data
	}
	return nil
}
// Envelope wraps a Payload with a signature so that the message may be authenticated
type Envelope struct {
	// A marshaled Payload
	Payload []byte `protobuf:"bytes,1,opt,name=payload,proto3" json:"payload,omitempty"`
	// A signature by the creator specified in the Payload header
	Signature []byte `protobuf:"bytes,2,opt,name=signature,proto3" json:"signature,omitempty"`
}
func (m *Envelope) Reset()                    { *m = Envelope{} }
func (m *Envelope) String() string            { return proto.CompactTextString(m) }
func (*Envelope) ProtoMessage()               {}
func (*Envelope) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{7} }
func (m *Envelope) GetPayload() []byte {
	if m != nil {
		return m.Payload
	}
	return nil
}
func (m *Envelope) GetSignature() []byte {
	if m != nil {
		return m.Signature
	}
	return nil
}
// This is finalized block structure to be shared among the orderer and peer
// Note that the BlockHeader chains to the previous BlockHeader, and the BlockData hash is embedded
// in the BlockHeader.  This makes it natural and obvious that the Data is included in the hash, but
// the Metadata is not.
type Block struct {
	Header   *BlockHeader   `protobuf:"bytes,1,opt,name=header" json:"header,omitempty"`
	Data     *BlockData     `protobuf:"bytes,2,opt,name=data" json:"data,omitempty"`
	Metadata *BlockMetadata `protobuf:"bytes,3,opt,name=metadata" json:"metadata,omitempty"`
}
func (m *Block) Reset()                    { *m = Block{} }
func (m *Block) String() string            { return proto.CompactTextString(m) }
func (*Block) ProtoMessage()               {}
func (*Block) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{8} }
func (m *Block) GetHeader() *BlockHeader {
	if m != nil {
		return m.Header
	}
	return nil
}
func (m *Block) GetData() *BlockData {
	if m != nil {
		return m.Data
	}
	return nil
}
func (m *Block) GetMetadata() *BlockMetadata {
	if m != nil {
		return m.Metadata
	}
	return nil
}
// BlockHeader is the element of the block which forms the block chain
// The block header is hashed using the configured chain hashing algorithm
// over the ASN.1 encoding of the BlockHeader
type BlockHeader struct {
	Number       uint64 `protobuf:"varint,1,opt,name=number" json:"number,omitempty"`
	PreviousHash []byte `protobuf:"bytes,2,opt,name=previous_hash,json=previousHash,proto3" json:"previous_hash,omitempty"`
	DataHash     []byte `protobuf:"bytes,3,opt,name=data_hash,json=dataHash,proto3" json:"data_hash,omitempty"`
}
func (m *BlockHeader) Reset()                    { *m = BlockHeader{} }
func (m *BlockHeader) String() string            { return proto.CompactTextString(m) }
func (*BlockHeader) ProtoMessage()               {}
func (*BlockHeader) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{9} }
func (m *BlockHeader) GetNumber() uint64 {
	if m != nil {
		return m.Number
	}
	return 0
}
func (m *BlockHeader) GetPreviousHash() []byte {
	if m != nil {
		return m.PreviousHash
	}
	return nil
}
func (m *BlockHeader) GetDataHash() []byte {
	if m != nil {
		return m.DataHash
	}
	return nil
}
type BlockData struct {
	Data [][]byte `protobuf:"bytes,1,rep,name=data,proto3" json:"data,omitempty"`
}
func (m *BlockData) Reset()                    { *m = BlockData{} }
func (m *BlockData) String() string            { return proto.CompactTextString(m) }
func (*BlockData) ProtoMessage()               {}
func (*BlockData) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{10} }
func (m *BlockData) GetData() [][]byte {
	if m != nil {
		return m.Data
	}
	return nil
}
type BlockMetadata struct {
	Metadata [][]byte `protobuf:"bytes,1,rep,name=metadata,proto3" json:"metadata,omitempty"`
}
func (m *BlockMetadata) Reset()                    { *m = BlockMetadata{} }
func (m *BlockMetadata) String() string            { return proto.CompactTextString(m) }
func (*BlockMetadata) ProtoMessage()               {}
func (*BlockMetadata) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{11} }
func (m *BlockMetadata) GetMetadata() [][]byte {
	if m != nil {
		return m.Metadata
	}
	return nil
}
var fileDescriptor0 = []byte{
	// 900 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x09, 0x6e, 0x88, 0x02, 0xff, 0x84, 0x55, 0xdf, 0x6e, 0xe3, 0xc4,
	0x1b, 0xad, 0xe3, 0xfc, 0x69, 0xbe, 0x34, 0xad, 0x3b, 0xd9, 0xfe, 0xd6, 0xbf, 0xc2, 0x6a, 0x23,
	0xc3, 0xa2, 0xd2, 0x4a, 0x89, 0x28, 0x37, 0x70, 0xe9, 0xd8, 0x93, 0xd6, 0x6a, 0xd6, 0x2e, 0x63,
	0x67, 0x11, 0xbb, 0x48, 0x96, 0x93, 0x4c, 0x13, 0x8b, 0xc4, 0x8e, 0x6c, 0xa7, 0x6a, 0x5f, 0x02,
	0x21, 0xc1, 0x0d, 0x17, 0xbc, 0x00, 0x4f, 0xc2, 0x5b, 0xf0, 0x12, 0x48, 0xdc, 0xa2, 0xf1, 0x8c,
	0xbd, 0x49, 0x59, 0x89, 0xab, 0xcc, 0x39, 0x73, 0x3c, 0xdf, 0x99, 0xf3, 0x7d, 0xb1, 0xa1, 0x33,
	0x8d, 0x57, 0xab, 0x38, 0xea, 0xf3, 0x9f, 0xde, 0x3a, 0x89, 0xb3, 0x18, 0xd5, 0x39, 0x3a, 0x7d,
	0x39, 0x8f, 0xe3, 0xf9, 0x92, 0xf6, 0x73, 0x76, 0xb2, 0xb9, 0xeb, 0x67, 0xe1, 0x8a, 0xa6, 0x59,
	0xb0, 0x5a, 0x73, 0xa1, 0xa6, 0x01, 0x8c, 0x82, 0x34, 0x33, 0xe2, 0xe8, 0x2e, 0x9c, 0xa3, 0x67,
	0x50, 0x0b, 0xa3, 0x19, 0x7d, 0x50, 0xa5, 0xae, 0x74, 0x56, 0x25, 0x1c, 0x68, 0xef, 0x60, 0xff,
	0x35, 0xcd, 0x82, 0x59, 0x90, 0x05, 0x4c, 0x71, 0x1f, 0x2c, 0x37, 0x34, 0x57, 0x1c, 0x10, 0x0e,
	0xd0, 0xd7, 0x00, 0x69, 0x38, 0x8f, 0x82, 0x6c, 0x93, 0xd0, 0x54, 0xad, 0x74, 0xe5, 0xb3, 0xd6,
	0xe5, 0xff, 0x7b, 0xc2, 0x51, 0xf1, 0xac, 0x5b, 0x28, 0xc8, 0x96, 0x58, 0xfb, 0x1e, 0x8e, 0xff,
	0x25, 0x40, 0x9f, 0x83, 0x52, 0x4a, 0xfc, 0x05, 0x0d, 0x66, 0x34, 0x11, 0x05, 0x8f, 0x4a, 0xfe,
	0x3a, 0xa7, 0xd1, 0xc7, 0xd0, 0x2c, 0x29, 0xb5, 0x92, 0x6b, 0xde, 0x13, 0xda, 0x5b, 0xa8, 0x0b,
	0xdd, 0x2b, 0x38, 0x9c, 0x2e, 0x82, 0x28, 0xa2, 0xcb, 0xdd, 0x03, 0xdb, 0x82, 0x15, 0xb2, 0x0f,
	0x55, 0xae, 0x7c, 0xb0, 0xb2, 0xf6, 0xa7, 0x04, 0x6d, 0x63, 0xe7, 0x61, 0x04, 0xd5, 0xec, 0x71,
	0xcd, 0xb3, 0xa9, 0x91, 0x7c, 0x8d, 0x54, 0x68, 0xdc, 0xd3, 0x24, 0x0d, 0xe3, 0x28, 0x3f, 0xa7,
	0x46, 0x0a, 0x88, 0xbe, 0x82, 0x66, 0xd9, 0x0d, 0x55, 0xee, 0x4a, 0x67, 0xad, 0xcb, 0xd3, 0x1e,
	0xef, 0x57, 0xaf, 0xe8, 0x57, 0xcf, 0x2b, 0x14, 0xe4, 0xbd, 0x18, 0xbd, 0x00, 0x28, 0xee, 0x12,
	0xce, 0xd4, 0x6a, 0x57, 0x3a, 0x6b, 0x92, 0xa6, 0x60, 0xac, 0x19, 0xea, 0x40, 0x2d, 0x7b, 0x60,
	0x3b, 0xb5, 0x7c, 0xa7, 0x9a, 0x3d, 0x58, 0x33, 0xd6, 0x38, 0xba, 0x8e, 0xa7, 0x0b, 0xb5, 0xce,
	0x5b, 0x9b, 0x03, 0x96, 0x1e, 0x7d, 0xc8, 0x68, 0x94, 0xfb, 0x6b, 0xf0, 0xf4, 0x4a, 0x42, 0xd3,
	0xe1, 0xc8, 0x7d, 0x12, 0xb7, 0x0a, 0x8d, 0x69, 0x42, 0x83, 0x2c, 0x2e, 0xf2, 0x2b, 0x20, 0x2b,
	0x10, 0xc5, 0xd1, 0xb4, 0x68, 0x02, 0x07, 0x1a, 0x86, 0xc6, 0x6d, 0xf0, 0xb8, 0x8c, 0x83, 0x19,
	0xfa, 0x0c, 0xea, 0x5b, 0xc9, 0xb7, 0x2e, 0x0f, 0x8b, 0x01, 0xe1, 0x47, 0x13, 0xb1, 0xcb, 0x52,
	0x64, 0xd3, 0x20, 0xce, 0xc9, 0xd7, 0xda, 0x00, 0xf6, 0x71, 0x74, 0x4f, 0x97, 0x31, 0x4f, 0x74,
	0xcd, 0x8f, 0x2c, 0x2c, 0x08, 0xf8, 0x1f, 0xb3, 0xf0, 0xa3, 0x04, 0xb5, 0xc1, 0x32, 0x9e, 0xfe,
	0x80, 0x2e, 0x9e, 0x38, 0xe9, 0x14, 0x4e, 0xf2, 0xed, 0x27, 0x76, 0x5e, 0x6d, 0xd9, 0x69, 0x5d,
	0x1e, 0xef, 0x48, 0xcd, 0x20, 0x0b, 0xb8, 0x43, 0xf4, 0x05, 0xec, 0xaf, 0xc4, 0x1c, 0x8b, 0x66,
	0x9e, 0xec, 0x48, 0x8b, 0x21, 0x27, 0xa5, 0x4c, 0x9b, 0x43, 0x6b, 0xab, 0x20, 0xfa, 0x1f, 0xd4,
	0xa3, 0xcd, 0x6a, 0x22, 0x5c, 0x55, 0x89, 0x40, 0xe8, 0x13, 0x68, 0xaf, 0x13, 0x7a, 0x1f, 0xc6,
	0x9b, 0xd4, 0x5f, 0x04, 0xe9, 0x42, 0xdc, 0xec, 0xa0, 0x20, 0xaf, 0x83, 0x74, 0x81, 0x3e, 0x82,
	0x26, 0x3b, 0x93, 0x0b, 0xe4, 0x5c, 0xb0, 0xcf, 0x08, 0xb6, 0xa9, 0xbd, 0x84, 0x66, 0x69, 0xb7,
	0x8c, 0x57, 0xea, 0xca, 0x65, 0xbc, 0x17, 0xd0, 0xde, 0x31, 0x89, 0x4e, 0xb7, 0x6e, 0xc3, 0x85,
	0x25, 0x3e, 0xff, 0x5d, 0x82, 0xba, 0x9b, 0x05, 0xd9, 0x26, 0x45, 0x2d, 0x68, 0x8c, 0xed, 0x1b,
	0xdb, 0xf9, 0xd6, 0x56, 0xf6, 0xd0, 0x01, 0x34, 0xdc, 0xb1, 0x61, 0x60, 0xd7, 0x55, 0xfe, 0x90,
	0x90, 0x02, 0xad, 0x81, 0x6e, 0xfa, 0x04, 0x7f, 0x33, 0xc6, 0xae, 0xa7, 0xfc, 0x24, 0xa3, 0x43,
	0x68, 0x0e, 0x1d, 0x32, 0xb0, 0x4c, 0x13, 0xdb, 0xca, 0xcf, 0x39, 0xb6, 0x1d, 0xcf, 0x1f, 0x3a,
	0x63, 0xdb, 0x54, 0x7e, 0x91, 0xd1, 0x0b, 0x50, 0x85, 0xda, 0xc7, 0xb6, 0x67, 0x79, 0xdf, 0xf9,
	0x9e, 0xe3, 0xf8, 0x23, 0x9d, 0x5c, 0x61, 0xe5, 0x37, 0x19, 0x9d, 0xc2, 0x89, 0x65, 0x7b, 0x98,
	0xd8, 0xfa, 0xc8, 0x77, 0x31, 0x79, 0x83, 0x89, 0x8f, 0x09, 0x71, 0x88, 0xf2, 0x97, 0x8c, 0x54,
	0xe8, 0x30, 0xca, 0x32, 0xb0, 0x3f, 0xb6, 0xf5, 0x37, 0xba, 0x35, 0xd2, 0x07, 0x23, 0xac, 0xfc,
	0x2d, 0x9f, 0xff, 0x2a, 0x01, 0xf0, 0x7c, 0x3d, 0xf6, 0x6f, 0x6c, 0x41, 0xe3, 0x35, 0x76, 0x5d,
	0xfd, 0x0a, 0x2b, 0x7b, 0x08, 0xa0, 0x6e, 0x38, 0xf6, 0xd0, 0xba, 0x52, 0x24, 0x74, 0x0c, 0x6d,
	0xbe, 0xf6, 0xc7, 0xb7, 0xa6, 0xee, 0x61, 0xa5, 0x82, 0x54, 0x78, 0x86, 0x6d, 0xd3, 0x21, 0x2e,
	0x26, 0xbe, 0x47, 0x74, 0xdb, 0xd5, 0x0d, 0xcf, 0x72, 0x6c, 0x45, 0x46, 0xcf, 0xa1, 0xe3, 0x10,
	0x13, 0x93, 0x27, 0x1b, 0x55, 0x74, 0x02, 0xc7, 0x26, 0x1e, 0x59, 0xcc, 0x9b, 0x8b, 0xf1, 0x8d,
	0x6f, 0xd9, 0x43, 0x47, 0xa9, 0x31, 0xda, 0xb8, 0xd6, 0x2d, 0xdb, 0x70, 0x4c, 0xec, 0xdf, 0xea,
	0xc6, 0x0d, 0xab, 0x5f, 0x3f, 0x7f, 0x07, 0x68, 0x27, 0x75, 0x8b, 0xbd, 0x6d, 0xd1, 0x21, 0x80,
	0x6b, 0x5d, 0xd9, 0xba, 0x37, 0x26, 0xd8, 0x55, 0xf6, 0xd0, 0x11, 0xb4, 0x46, 0xba, 0xeb, 0xf9,
	0xa5, 0xd5, 0xe7, 0xd0, 0xd9, 0xaa, 0xea, 0xfa, 0x43, 0x6b, 0xe4, 0x61, 0xa2, 0x54, 0xd8, 0xe5,
	0x84, 0x2d, 0x45, 0x1e, 0xb8, 0xf0, 0x69, 0x9c, 0xcc, 0x7b, 0x8b, 0xc7, 0x35, 0x4d, 0x96, 0x74,
	0x36, 0xa7, 0x49, 0xef, 0x2e, 0x98, 0x24, 0xe1, 0x94, 0xbf, 0x5b, 0x52, 0x31, 0x9c, 0x6f, 0x2f,
	0xe6, 0x61, 0xb6, 0xd8, 0x4c, 0x18, 0xec, 0x6f, 0x89, 0xfb, 0x5c, 0xcc, 0x3f, 0x1c, 0xa9, 0xf8,
	0xb8, 0x4c, 0xea, 0x39, 0xfc, 0xf2, 0x9f, 0x00, 0x00, 0x00, 0xff, 0xff, 0xa1, 0xcb, 0xe1, 0xb4,
	0x74, 0x06, 0x00, 0x00,
}

/*** fabric/orderer/common/bootstrap/bootstrap.go ***/
// Helper defines the functions a bootstrapping implementation should provide.
type BootstrapHelper interface { //WAS:Helper
	// GenesisBlock should return the genesis block required to bootstrap
	// the ledger (be it reading from the filesystem, generating it, etc.)
	GenesisBlock() *Block //SOURCE:ab.Block
}

/*** fabric/protos/common/configtx.go ***/
func NewConfigGroup() *ConfigGroup {
	return &ConfigGroup{
		Groups:   make(map[string]*ConfigGroup),
		Values:   make(map[string]*ConfigValue),
		Policies: make(map[string]*ConfigPolicy),
	}
}

/*** fabric/common/policies/implicitmeta_util.go ***/
// ImplicitMetaPolicyWithSubPolicy creates an implicitmeta policy
func ImplicitMetaPolicyWithSubPolicy(subPolicyName string, rule ImplicitMetaPolicy_Rule) *ConfigPolicy { //SOURCE:cb.ImplicitMetaPolicy_Rule //SOURCE:cb.ConfigPolicy
	return &ConfigPolicy{ //SOURCE:cb.ConfigPolicy
		Policy: &Policy{ //SOURCE:cb.Policy
			Type: int32(Policy_IMPLICIT_META), //int32=3 //SOURCE:cb.Policy_IMPLICIT_META
			Value: MarshalOrPanic(&ImplicitMetaPolicy{ //SOURCE:cb.ImplicitMetaPolicy //SOURCE:utils.MarshalOrPanic
				Rule:      rule,
				SubPolicy: subPolicyName,
			}),
		},
	}
}
// TemplateImplicitMetaPolicy creates a policy at the specified path with the given policyName and subPolicyName
func TemplateImplicitMetaPolicyWithSubPolicy(path []string, policyName string, subPolicyName string, rule ImplicitMetaPolicy_Rule) *ConfigGroup { //SOURCE:cb.ImplicitMetaPolicy_Rule //SOURCE:cb.ConfigGroup
	root := NewConfigGroup() //SOURCE:cb.NewConfigGroup
	group := root
	for _, element := range path {
		group.Groups[element] = NewConfigGroup() //SOURCE:cb.NewConfigGroup
		group = group.Groups[element]
	}

	group.Policies[policyName] = ImplicitMetaPolicyWithSubPolicy(subPolicyName, rule)
	return root
}
// TemplateImplicitMetaPolicy creates a policy at the specified path with the given policyName
// It utilizes the policyName for the subPolicyName as well, as this is the standard usage pattern
func TemplateImplicitMetaPolicy(path []string, policyName string, rule ImplicitMetaPolicy_Rule) *ConfigGroup { //SOURCE:cb.ImplicitMetaPolicy_Rule //SOURCE:cb.ConfigGroup
	return TemplateImplicitMetaPolicyWithSubPolicy(path, policyName, policyName, rule)
}
// TempateImplicitMetaAnyPolicy returns TemplateImplicitMetaPolicy with cb.ImplicitMetaPolicy_ANY as the rule
func TemplateImplicitMetaAnyPolicy(path []string, policyName string) *ConfigGroup { //SOURCE:cb.ConfigGroup
	return TemplateImplicitMetaPolicy(path, policyName, ImplicitMetaPolicy_ANY) //int32=0 //SOURCE:cb.ImplicitMetaPolicy_ANY
}
// TempateImplicitMetaAnyPolicy returns TemplateImplicitMetaPolicy with cb.ImplicitMetaPolicy_MAJORITY as the rule
func TemplateImplicitMetaMajorityPolicy(path []string, policyName string) *ConfigGroup { //SOURCE:cb.ConfigGroup
	return TemplateImplicitMetaPolicy(path, policyName, ImplicitMetaPolicy_MAJORITY) //int32=2 //SOURCE:cb.ImplicitMetaPolicy_ANY
}

/*** fabric/bccsp/opts.go ***/
const (
	// ECDSA Elliptic Curve Digital Signature Algorithm (key gen, import, sign, verify),
	// at default security level.
	// Each BCCSP may or may not support default security level. If not supported than
	// an error will be returned.
	ECDSA = "ECDSA"
	// ECDSA Elliptic Curve Digital Signature Algorithm over P-256 curve
	ECDSAP256 = "ECDSAP256"
	// ECDSA Elliptic Curve Digital Signature Algorithm over P-384 curve
	ECDSAP384 = "ECDSAP384"
	// ECDSAReRand ECDSA key re-randomization
	ECDSAReRand = "ECDSA_RERAND"
	// RSA at the default security level.
	// Each BCCSP may or may not support default security level. If not supported than
	// an error will be returned.
	RSA = "RSA"
	// RSA at 1024 bit security level.
	RSA1024 = "RSA1024"
	// RSA at 2048 bit security level.
	RSA2048 = "RSA2048"
	// RSA at 3072 bit security level.
	RSA3072 = "RSA3072"
	// RSA at 4096 bit security level.
	RSA4096 = "RSA4096"
	// AES Advanced Encryption Standard at the default security level.
	// Each BCCSP may or may not support default security level. If not supported than
	// an error will be returned.
	AES = "AES"
	// AES Advanced Encryption Standard at 128 bit security level
	AES128 = "AES128"
	// AES Advanced Encryption Standard at 192 bit security level
	AES192 = "AES192"
	// AES Advanced Encryption Standard at 256 bit security level
	AES256 = "AES256"
	// HMAC keyed-hash message authentication code
	HMAC = "HMAC"
	// HMACTruncated256 HMAC truncated at 256 bits.
	HMACTruncated256 = "HMAC_TRUNCATED_256"
	// SHA Secure Hash Algorithm using default family.
	// Each BCCSP may or may not support default security level. If not supported than
	// an error will be returned.
	SHA = "SHA"
	// SHA2 is an identifier for SHA2 hash family
	SHA2 = "SHA2"
	// SHA3 is an identifier for SHA3 hash family
	SHA3 = "SHA3"
	// SHA256
	SHA256 = "SHA256"
	// SHA384
	SHA384 = "SHA384"
	// SHA3_256
	SHA3_256 = "SHA3_256"
	// SHA3_384
	SHA3_384 = "SHA3_384"
	// X509Certificate Label for X509 certificate related operation
	X509Certificate = "X509Certificate"
)
// ECDSAKeyGenOpts contains options for ECDSA key generation.
type ECDSAKeyGenOpts struct {
	Temporary bool
}
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *ECDSAKeyGenOpts) Algorithm() string {
	return ECDSA
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *ECDSAKeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}
// ECDSAPKIXPublicKeyImportOpts contains options for ECDSA public key importation in PKIX format
type ECDSAPKIXPublicKeyImportOpts struct {
	Temporary bool
}
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
// ECDSAReRandKeyOpts contains options for ECDSA key re-randomization.
type ECDSAReRandKeyOpts struct {
	Temporary bool
	Expansion []byte
}
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
// AESKeyGenOpts contains options for AES key generation at default security level
type AESKeyGenOpts struct {
	Temporary bool
}
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *AESKeyGenOpts) Algorithm() string {
	return AES
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *AESKeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}
// AESCBCPKCS7ModeOpts contains options for AES encryption in CBC mode
// with PKCS7 padding.
type AESCBCPKCS7ModeOpts struct{}
// HMACTruncated256AESDeriveKeyOpts contains options for HMAC truncated
// at 256 bits key derivation.
type HMACTruncated256AESDeriveKeyOpts struct {
	Temporary bool
	Arg       []byte
}
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
// AES256ImportKeyOpts contains options for importing AES 256 keys.
type AES256ImportKeyOpts struct {
	Temporary bool
}
// Algorithm returns the key importation algorithm identifier (to be used).
func (opts *AES256ImportKeyOpts) Algorithm() string {
	return AES
}
// Ephemeral returns true if the key generated has to be ephemeral,
// false otherwise.
func (opts *AES256ImportKeyOpts) Ephemeral() bool {
	return opts.Temporary
}
// HMACImportKeyOpts contains options for importing HMAC keys.
type HMACImportKeyOpts struct {
	Temporary bool
}
// Algorithm returns the key importation algorithm identifier (to be used).
func (opts *HMACImportKeyOpts) Algorithm() string {
	return HMAC
}
// Ephemeral returns true if the key generated has to be ephemeral,
// false otherwise.
func (opts *HMACImportKeyOpts) Ephemeral() bool {
	return opts.Temporary
}
// SHAOpts contains options for computing SHA.
type SHAOpts struct {
}
// Algorithm returns the hash algorithm identifier (to be used).
func (opts *SHAOpts) Algorithm() string {
	return SHA
}
// RSAKeyGenOpts contains options for RSA key generation.
type RSAKeyGenOpts struct {
	Temporary bool
}
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *RSAKeyGenOpts) Algorithm() string {
	return RSA
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *RSAKeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}
// ECDSAGoPublicKeyImportOpts contains options for RSA key importation from rsa.PublicKey
type RSAGoPublicKeyImportOpts struct {
	Temporary bool
}
// Algorithm returns the key importation algorithm identifier (to be used).
func (opts *RSAGoPublicKeyImportOpts) Algorithm() string {
	return RSA
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *RSAGoPublicKeyImportOpts) Ephemeral() bool {
	return opts.Temporary
}
// X509PublicKeyImportOpts contains options for importing public keys from an x509 certificate
type X509PublicKeyImportOpts struct {
	Temporary bool
}
// Algorithm returns the key importation algorithm identifier (to be used).
func (opts *X509PublicKeyImportOpts) Algorithm() string {
	return X509Certificate
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *X509PublicKeyImportOpts) Ephemeral() bool {
	return opts.Temporary
}

/*** fabric/bccsp/aesopts.go ***/
// AES128KeyGenOpts contains options for AES key generation at 128 security level
type AES128KeyGenOpts struct {
	Temporary bool
}
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *AES128KeyGenOpts) Algorithm() string {
	return AES128
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *AES128KeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}
// AES192KeyGenOpts contains options for AES key generation at 192  security level
type AES192KeyGenOpts struct {
	Temporary bool
}
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *AES192KeyGenOpts) Algorithm() string {
	return AES192
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *AES192KeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}
// AES256KeyGenOpts contains options for AES key generation at 256 security level
type AES256KeyGenOpts struct {
	Temporary bool
}
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *AES256KeyGenOpts) Algorithm() string {
	return AES256
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *AES256KeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}

/*** fabric/bccsp/ecdsaopts.go ***/
// ECDSAP256KeyGenOpts contains options for ECDSA key generation with curve P-256.
type ECDSAP256KeyGenOpts struct {
	Temporary bool
}
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
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *ECDSAP384KeyGenOpts) Algorithm() string {
	return ECDSAP384
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *ECDSAP384KeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}

/*** fabric/bccsp/rsaopts.go ***/
// RSA1024KeyGenOpts contains options for RSA key generation at 1024 security.
type RSA1024KeyGenOpts struct {
	Temporary bool
}
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *RSA1024KeyGenOpts) Algorithm() string {
	return RSA1024
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *RSA1024KeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}
// RSA2048KeyGenOpts contains options for RSA key generation at 2048 security.
type RSA2048KeyGenOpts struct {
	Temporary bool
}
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *RSA2048KeyGenOpts) Algorithm() string {
	return RSA2048
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *RSA2048KeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}
// RSA3072KeyGenOpts contains options for RSA key generation at 3072 security.
type RSA3072KeyGenOpts struct {
	Temporary bool
}
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *RSA3072KeyGenOpts) Algorithm() string {
	return RSA3072
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *RSA3072KeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}
// RSA4096KeyGenOpts contains options for RSA key generation at 4096 security.
type RSA4096KeyGenOpts struct {
	Temporary bool
}
// Algorithm returns the key generation algorithm identifier (to be used).
func (opts *RSA4096KeyGenOpts) Algorithm() string {
	return RSA4096
}
// Ephemeral returns true if the key to generate has to be ephemeral,
// false otherwise.
func (opts *RSA4096KeyGenOpts) Ephemeral() bool {
	return opts.Temporary
}

/*** fabric/protos/utils/txutils.go ***/
// GetEnvelopeFromBlock gets an envelope from a block's Data field.
func GetEnvelopeFromBlock(data []byte) (*Envelope, error) { //SOURCE:common.Envelope
	//Block always begins with an envelope
	var err error
	env := &Envelope{} //SOURCE:common.Envelope
	if err = proto.Unmarshal(data, env); err != nil {
		return nil, fmt.Errorf("Error getting envelope(%s)", err)
	}
	return env, nil
}

/*** fabric/common/config/standardvalues.go ***/
type standardValues struct {
	lookup map[string]proto.Message
}
// NewStandardValues accepts a structure which must contain only protobuf message
// types.  The structure may embed other (non-pointer) structures which satisfy
// the same condition.  NewStandard values will instantiate memory for all the proto
// messages and build a lookup map from structure field name to proto message instance
// This is a useful way to easily implement the Values interface
func NewStandardValues(protosStructs ...interface{}) (*standardValues, error) {
	sv := &standardValues{
		lookup: make(map[string]proto.Message),
	}
	for _, protosStruct := range protosStructs {
		logger.Debugf("Initializing protos for %T\n", protosStruct)
		if err := sv.initializeProtosStruct(reflect.ValueOf(protosStruct)); err != nil {
			return nil, err
		}
	}
	return sv, nil
}
// Deserialize looks up the backing Values proto of the given name, unmarshals the given bytes
// to populate the backing message structure, and returns a referenced to the retained deserialized
// message (or an error, either because the key did not exist, or there was an an error unmarshaling
func (sv *standardValues) Deserialize(key string, value []byte) (proto.Message, error) {
	msg, ok := sv.lookup[key]
	if !ok {
		return nil, fmt.Errorf("Unexpected key %s", key)
	}
	err := proto.Unmarshal(value, msg)
	if err != nil {
		return nil, err
	}
	return msg, nil
}
func (sv *standardValues) initializeProtosStruct(objValue reflect.Value) error {
	objType := objValue.Type()
	if objType.Kind() != reflect.Ptr {
		return fmt.Errorf("Non pointer type")
	}
	if objType.Elem().Kind() != reflect.Struct {
		return fmt.Errorf("Non struct type")
	}
	numFields := objValue.Elem().NumField()
	for i := 0; i < numFields; i++ {
		structField := objType.Elem().Field(i)
		logger.Debugf("Processing field: %s\n", structField.Name)
		switch structField.Type.Kind() {
		case reflect.Ptr:
			fieldPtr := objValue.Elem().Field(i)
			if !fieldPtr.CanSet() {
				return fmt.Errorf("Cannot set structure field %s (unexported?)", structField.Name)
			}
			fieldPtr.Set(reflect.New(structField.Type.Elem()))
		default:
			return fmt.Errorf("Bad type supplied: %s", structField.Type.Kind())
		}
		proto, ok := objValue.Elem().Field(i).Interface().(proto.Message)
		if !ok {
			return fmt.Errorf("Field type %T does not implement proto.Message", objValue.Elem().Field(i))
		}
		_, ok = sv.lookup[structField.Name]
		if ok {
			return fmt.Errorf("Ambiguous field name specified, multiple occurrences of %s", structField.Name)
		}
		sv.lookup[structField.Name] = proto
	}
	return nil
}

/*** fabric/common/config/channel.go ***/
// Channel config keys
const (
	// ConsortiumKey is the key for the cb.ConfigValue for the Consortium message
	ConsortiumKey = "Consortium"
	// HashingAlgorithmKey is the cb.ConfigItem type key name for the HashingAlgorithm message
	HashingAlgorithmKey = "HashingAlgorithm"
	// BlockDataHashingStructureKey is the cb.ConfigItem type key name for the BlockDataHashingStructure message
	BlockDataHashingStructureKey = "BlockDataHashingStructure"
	// OrdererAddressesKey is the cb.ConfigItem type key name for the OrdererAddresses message
	OrdererAddressesKey = "OrdererAddresses"
	// GroupKey is the name of the channel group
	ChannelGroupKey = "Channel"
)
// ChannelProtos is where the proposed configuration is unmarshaled into
type ChannelProtos struct {
	HashingAlgorithm          *HashingAlgorithm //SOURCE:cb.HashingAlgorithm
	BlockDataHashingStructure *BlockDataHashingStructure //SOURCE:cb.BlockDataHashingStructure
	OrdererAddresses          *OrdererAddresses //SOURCE:cb.OrdererAddresses
	Consortium                *ConsortiumPROTO //WAS:Consortium //SOURCE:cb.Consortium
}
type channelConfigSetter struct {
	target **ChannelConfig
	*ChannelConfig
}
func (ccs *channelConfigSetter) Commit() {
	*(ccs.target) = ccs.ChannelConfig
}
// ChannelGroup
type ChannelGroup struct {
	*ChannelConfig
	*ProposerCONFIG //WAS:Proposer
	mspConfigHandler *MSPConfigHandler //SOURCE:msp.MSPConfigHandler
}
func NewChannelGroup(mspConfigHandler *MSPConfigHandler) *ChannelGroup { //SOURCE:msp.MSPConfigHandler
	cg := &ChannelGroup{
		ChannelConfig:    NewChannelConfig(),
		mspConfigHandler: mspConfigHandler,
	}
	cg.ProposerCONFIG = NewProposer(cg) //WAS:Proposer
	return cg
}
// Allocate creates new config resources for a pending config update
func (cg *ChannelGroup) Allocate() Values {
	return &channelConfigSetter{
		ChannelConfig: NewChannelConfig(),
		target:        &cg.ChannelConfig,
	}
}
// OrdererConfig returns the orderer config associated with this channel
func (cg *ChannelGroup) OrdererConfig() *OrdererGroup {
	return cg.ChannelConfig.ordererConfig
}
// ApplicationConfig returns the application config associated with this channel
func (cg *ChannelGroup) ApplicationConfig() *ApplicationGroup {
	return cg.ChannelConfig.appConfig
}
// ConsortiumsConfig returns the consortium config associated with this channel if it exists
func (cg *ChannelGroup) ConsortiumsConfig() *ConsortiumsGroup {
	return cg.ChannelConfig.consortiumsConfig
}
// NewGroup instantiates either a new application or orderer config
func (cg *ChannelGroup) NewGroup(group string) (ValueProposer, error) {
	switch group {
	case ApplicationGroupKey:
		return NewApplicationGroup(cg.mspConfigHandler), nil
	case OrdererGroupKey:
		return NewOrdererGroup(cg.mspConfigHandler), nil
	case ConsortiumsGroupKey:
		return NewConsortiumsGroup(cg.mspConfigHandler), nil
	default:
		return nil, fmt.Errorf("Disallowed channel group: %s", group)
	}
}
// //NOT IN FABRIC - NEEDED?
// // BlockDataHashingStructure returns the width to use when forming the block data hashing structure
// func (cg *ChannelGroup) BlockDataHashingStructureWidth() uint32 {
// 	return cg.protos.BlockDataHashingStructure.Width
// }
// ChannelConfig stores the channel configuration
type ChannelConfig struct {
	*standardValues
	protos *ChannelProtos
	hashingAlgorithm func(input []byte) []byte
	appConfig         *ApplicationGroup
	ordererConfig     *OrdererGroup
	consortiumsConfig *ConsortiumsGroup
}
// NewChannelConfig creates a new ChannelConfig
func NewChannelConfig() *ChannelConfig {
	cc := &ChannelConfig{
		protos: &ChannelProtos{},
	}
	var err error
	cc.standardValues, err = NewStandardValues(cc.protos)
	if err != nil {
		logger.Panicf("Programming error: %s", err)
	}
	return cc
}
// HashingAlgorithm returns a function pointer to the chain hashing algorihtm
func (cc *ChannelConfig) HashingAlgorithm() func(input []byte) []byte {
	return cc.hashingAlgorithm
}
// BlockDataHashingStructure returns the width to use when forming the block data hashing structure
func (cc *ChannelConfig) BlockDataHashingStructureWidth() uint32 {
	return cc.protos.BlockDataHashingStructure.Width
}
// OrdererAddresses returns the list of valid orderer addresses to connect to to invoke Broadcast/Deliver
func (cc *ChannelConfig) OrdererAddresses() []string {
	return cc.protos.OrdererAddresses.Addresses
}
// ConsortiumName returns the name of the consortium this channel was created under
func (cc *ChannelConfig) ConsortiumName() string {
	return cc.protos.Consortium.Name
}
// Validate inspects the generated configuration protos, ensures that the values are correct, and
// sets the ChannelConfig fields that may be referenced after Commit
func (cc *ChannelConfig) Validate(tx interface{}, groups map[string]ValueProposer) error {
	for _, validator := range []func() error{
		cc.validateHashingAlgorithm,
		cc.validateBlockDataHashingStructure,
		cc.validateOrdererAddresses,
	} {
		if err := validator(); err != nil {
			return err
		}
	}
	var ok bool
	for key, value := range groups {
		switch key {
		case ApplicationGroupKey:
			cc.appConfig, ok = value.(*ApplicationGroup)
			if !ok {
				return fmt.Errorf("Application group was not Application config")
			}
		case OrdererGroupKey:
			cc.ordererConfig, ok = value.(*OrdererGroup)
			if !ok {
				return fmt.Errorf("Orderer group was not Orderer config")
			}
		case ConsortiumsGroupKey:
			cc.consortiumsConfig, ok = value.(*ConsortiumsGroup)
			if !ok {
				return fmt.Errorf("Consortiums group was no Consortium config")
			}
		default:
			return fmt.Errorf("Disallowed channel group: %s", key)
		}
	}
	return nil
}
func (cc *ChannelConfig) validateHashingAlgorithm() error {
	switch cc.protos.HashingAlgorithm.Name {
	case SHA256: //SOURCE:bccsp.SHA256
		cc.hashingAlgorithm = ComputeSHA256 //SOURCE:util.ComputeSHA256
	case SHA3_256: //SOURCE:bccsp.SHA3_256
		cc.hashingAlgorithm = ComputeSHA3256 //SOURCE:util.ComputeSHA3256
	default:
		return fmt.Errorf("Unknown hashing algorithm type: %s", cc.protos.HashingAlgorithm.Name)
	}
	return nil
}
func (cc *ChannelConfig) validateBlockDataHashingStructure() error {
	if cc.protos.BlockDataHashingStructure.Width != math.MaxUint32 {
		return fmt.Errorf("BlockDataHashStructure width only supported at MaxUint32 in this version")
	}
	return nil
}
func (cc *ChannelConfig) validateOrdererAddresses() error {
	if len(cc.protos.OrdererAddresses.Addresses) == 0 {
		return fmt.Errorf("Must set some OrdererAddresses")
	}
	return nil
}

/*** fabric/common/crypto/random.go ***/
// NonceSize is the default NonceSize
const NonceSize = 24
// GetRandomBytes returns len random looking bytes
func GetRandomBytes(len int) ([]byte, error) {
	key := make([]byte, len)
	// TODO: rand could fill less bytes then len
	_, err := rand.Read(key)
	if err != nil {
		return nil, err
	}
	return key, nil
}
// GetRandomNonce returns a random byte array of length NonceSize
func GetRandomNonce() ([]byte, error) {
	return GetRandomBytes(NonceSize)
}

/*** fabric/protos/utils/proputils.go ***/
// ComputeProposalTxID computes TxID as the Hash computed
// over the concatenation of nonce and creator.
func ComputeProposalTxID(nonce, creator []byte) (string, error) {
	// TODO: Get the Hash function to be used from
	// channel configuration
	digest, err := GetDefault().Hash( //SOURCE:factory.GetDefault
		append(nonce, creator...),
		&SHA256Opts{}) //SOURCE:bccsp.SHA256Opts
	if err != nil {
		return "", err
	}
	return hex.EncodeToString(digest), nil
}

/*** fabric/protos/utils/commonutils.go ***/
// MarshalOrPanic serializes a protobuf message and panics if this operation fails.
func MarshalOrPanic(pb proto.Message) []byte {
	data, err := proto.Marshal(pb)
	if err != nil {
		panic(err)
	}
	return data
}
// CreateNonceOrPanic generates a nonce using the common/crypto package
// and panics if this operation fails.
func CreateNonceOrPanic() []byte {
	nonce, err := GetRandomNonce() //SOURCE:crypto.GetRandomNonce
	if err != nil {
		panic(fmt.Errorf("Cannot generate random nonce: %s", err))
	}
	return nonce
}
// ExtractEnvelope retrieves the requested envelope from a given block and unmarshals it.
func ExtractEnvelope(block *Block, index int) (*Envelope, error) { //SOURCE:cb.Block //SOURCE:cb.Envelope
	if block.Data == nil {
		return nil, fmt.Errorf("No data in block")
	}
	envelopeCount := len(block.Data.Data)
	if index < 0 || index >= envelopeCount {
		return nil, fmt.Errorf("Envelope index out of bounds")
	}
	marshaledEnvelope := block.Data.Data[index]
	envelope, err := GetEnvelopeFromBlock(marshaledEnvelope)
	if err != nil {
		return nil, fmt.Errorf("Block data does not carry an envelope at index %d: %s", index, err)
	}
	return envelope, nil
}
// UnmarshalPayload unmarshals bytes to a Payload structure
func UnmarshalPayload(encoded []byte) (*Payload, error) { //SOURCE:cb.Payload
	payload := &Payload{} //SOURCE:cb.Payload
	err := proto.Unmarshal(encoded, payload)
	if err != nil {
		return nil, err
	}
	return payload, err
}
// UnmarshalEnvelope unmarshals bytes to an Envelope structure
func UnmarshalEnvelope(encoded []byte) (*Envelope, error) { //SOURCE:cb.Envelope
	envelope := &Envelope{} //SOURCE:cb.Envelope
	err := proto.Unmarshal(encoded, envelope)
	if err != nil {
		return nil, err
	}
	return envelope, err
}
// MakeChannelHeader creates a ChannelHeader.
func MakeChannelHeader(headerType HeaderType, version int32, chainID string, epoch uint64) *ChannelHeader { //SOURCE:cb.HeaderType //SOURCE:cb.ChannelHeader
	return &ChannelHeader{ //SOURCE:cb.ChannelHeader
		Type:    int32(headerType),
		Version: version,
		Timestamp: &timestamp.Timestamp{
			Seconds: time.Now().Unix(),
			Nanos:   0,
		},
		ChannelId: chainID,
		Epoch:     epoch,
	}
}
// MakeSignatureHeader creates a SignatureHeader.
func MakeSignatureHeader(serializedCreatorCertChain []byte, nonce []byte) *SignatureHeader { //SOURCE:cb.SignatureHeader
	return &SignatureHeader{ //SOURCE:cb.SignatureHeader
		Creator: serializedCreatorCertChain,
		Nonce:   nonce,
	}
}
func SetTxID(channelHeader *ChannelHeader, signatureHeader *SignatureHeader) error { //SOURCE:cb.ChannelHeader //SOURCE:cb.SignatureHeader
	txid, err := ComputeProposalTxID(
		signatureHeader.Nonce,
		signatureHeader.Creator,
	)
	if err != nil {
		return err
	}
	channelHeader.TxId = txid
	return nil
}
// MakePayloadHeader creates a Payload Header.
func MakePayloadHeader(ch *ChannelHeader, sh *SignatureHeader) *Header { //SOURCE:cb.ChannelHeader //SOURCE:cb.SignatureHeader //SOURCE:cb.Header
	return &Header{ //SOURCE:cb.Header
		ChannelHeader:   MarshalOrPanic(ch),
		SignatureHeader: MarshalOrPanic(sh),
	}
}
// UnmarshalChannelHeader returns a ChannelHeader from bytes
func UnmarshalChannelHeader(bytes []byte) (*ChannelHeader, error) { //SOURCE:cb.ChannelHeader
	chdr := &ChannelHeader{} //SOURCE:cb.ChannelHeader
	err := proto.Unmarshal(bytes, chdr)
	if err != nil {
		return nil, fmt.Errorf("UnmarshalChannelHeader failed, err %s", err)
	}
	return chdr, nil
}

/*** fabric/protos/common/configuration.pb.go ***/
// HashingAlgorithm is encoded into the configuration transaction as  a configuration item of type Chain
// with a Key of "HashingAlgorithm" and a Value of  HashingAlgorithm as marshaled protobuf bytes
type HashingAlgorithm struct {
	// Currently supported algorithms are: SHAKE256
	Name string `protobuf:"bytes,1,opt,name=name" json:"name,omitempty"`
}
func (m *HashingAlgorithm) Reset()                    { *m = HashingAlgorithm{} }
func (m *HashingAlgorithm) String() string            { return proto.CompactTextString(m) }
func (*HashingAlgorithm) ProtoMessage()               {}
func (*HashingAlgorithm) Descriptor() ([]byte, []int) { return fileDescriptor2, []int{0} }
func (m *HashingAlgorithm) GetName() string {
	if m != nil {
		return m.Name
	}
	return ""
}
// BlockDataHashingStructure is encoded into the configuration transaction as a configuration item of
// type Chain with a Key of "BlockDataHashingStructure" and a Value of HashingAlgorithm as marshaled protobuf bytes
type BlockDataHashingStructure struct {
	// width specifies the width of the Merkle tree to use when computing the BlockDataHash
	// in order to replicate flat hashing, set this width to MAX_UINT32
	Width uint32 `protobuf:"varint,1,opt,name=width" json:"width,omitempty"`
}
func (m *BlockDataHashingStructure) Reset()                    { *m = BlockDataHashingStructure{} }
func (m *BlockDataHashingStructure) String() string            { return proto.CompactTextString(m) }
func (*BlockDataHashingStructure) ProtoMessage()               {}
func (*BlockDataHashingStructure) Descriptor() ([]byte, []int) { return fileDescriptor2, []int{1} }
func (m *BlockDataHashingStructure) GetWidth() uint32 {
	if m != nil {
		return m.Width
	}
	return 0
}
// OrdererAddresses is encoded into the configuration transaction as a configuration item of type Chain
// with a Key of "OrdererAddresses" and a Value of OrdererAddresses as marshaled protobuf bytes
type OrdererAddresses struct {
	Addresses []string `protobuf:"bytes,1,rep,name=addresses" json:"addresses,omitempty"`
}
func (m *OrdererAddresses) Reset()                    { *m = OrdererAddresses{} }
func (m *OrdererAddresses) String() string            { return proto.CompactTextString(m) }
func (*OrdererAddresses) ProtoMessage()               {}
func (*OrdererAddresses) Descriptor() ([]byte, []int) { return fileDescriptor2, []int{2} }
func (m *OrdererAddresses) GetAddresses() []string {
	if m != nil {
		return m.Addresses
	}
	return nil
}
// Consortium represents the consortium context in which the channel was created
type ConsortiumPROTO struct { //WAS:Consortium
	Name string `protobuf:"bytes,1,opt,name=name" json:"name,omitempty"`
}
func (m *ConsortiumPROTO) Reset()                    { *m = ConsortiumPROTO{} } //WAS:Consortium
func (m *ConsortiumPROTO) String() string            { return proto.CompactTextString(m) } //WAS:Consortium
func (*ConsortiumPROTO) ProtoMessage()               {} //WAS:Consortium
func (*ConsortiumPROTO) Descriptor() ([]byte, []int) { return fileDescriptor2, []int{3} } //WAS:Consortium
func (m *ConsortiumPROTO) GetName() string { //WAS:Consortium
	if m != nil {
		return m.Name
	}
	return ""
}
var fileDescriptor2 = []byte{
	// 230 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x09, 0x6e, 0x88, 0x02, 0xff, 0x6c, 0x8f, 0xc1, 0x4a, 0x03, 0x31,
	0x10, 0x86, 0x59, 0xd4, 0xc2, 0x0e, 0x08, 0x25, 0x78, 0xa8, 0xe2, 0x61, 0x59, 0x44, 0x0a, 0xc2,
	0x46, 0xf1, 0x09, 0x5a, 0x3d, 0x78, 0x13, 0xb6, 0x37, 0x6f, 0xd9, 0x24, 0x4d, 0x82, 0xbb, 0x99,
	0x32, 0x99, 0x20, 0xbe, 0xbd, 0xb8, 0x51, 0xf4, 0xd0, 0xdb, 0x7c, 0x33, 0xdf, 0x0f, 0xf3, 0xc3,
	0x95, 0xc6, 0x69, 0xc2, 0x28, 0x35, 0xc6, 0x7d, 0x70, 0x99, 0x14, 0x07, 0x8c, 0xdd, 0x81, 0x90,
	0x51, 0x2c, 0xca, 0xad, 0xbd, 0x85, 0xe5, 0x8b, 0x4a, 0x3e, 0x44, 0xb7, 0x19, 0x1d, 0x52, 0x60,
	0x3f, 0x09, 0x01, 0xa7, 0x51, 0x4d, 0x76, 0x55, 0x35, 0xd5, 0xba, 0xee, 0xe7, 0xb9, 0x7d, 0x80,
	0xcb, 0xed, 0x88, 0xfa, 0xfd, 0x59, 0xb1, 0xfa, 0x09, 0xec, 0x98, 0xb2, 0xe6, 0x4c, 0x56, 0x5c,
	0xc0, 0xd9, 0x47, 0x30, 0xec, 0xe7, 0xc4, 0x79, 0x5f, 0xa0, 0xbd, 0x87, 0xe5, 0x2b, 0x19, 0x4b,
	0x96, 0x36, 0xc6, 0x90, 0x4d, 0xc9, 0x26, 0x71, 0x0d, 0xb5, 0xfa, 0x85, 0x55, 0xd5, 0x9c, 0xac,
	0xeb, 0xfe, 0x6f, 0xd1, 0x36, 0x00, 0x4f, 0x18, 0x13, 0x12, 0x87, 0x7c, 0xf4, 0x8d, 0xed, 0x0e,
	0x6e, 0x90, 0x5c, 0xe7, 0x3f, 0x0f, 0x96, 0x46, 0x6b, 0x9c, 0xa5, 0x6e, 0xaf, 0x06, 0x0a, 0xba,
	0xd4, 0x4a, 0x5d, 0xa9, 0xf5, 0x76, 0xe7, 0x02, 0xfb, 0x3c, 0x7c, 0xa3, 0xfc, 0x27, 0xcb, 0x22,
	0xcb, 0x22, 0xcb, 0x22, 0x0f, 0x8b, 0x19, 0x1f, 0xbf, 0x02, 0x00, 0x00, 0xff, 0xff, 0xb6, 0x15,
	0xb9, 0xb4, 0x30, 0x01, 0x00, 0x00,
}

/*** fabric/common/config/channel_util.go ***/
const defaultHashingAlgorithm = SHA256
func configGroup(key string, value []byte) *ConfigGroup { //SOURCE:cb.ConfigGroup
	result := NewConfigGroup() //SOURCE:cb.NewConfigGroup
	result.Values[key] = &ConfigValue{ //SOURCE:cb.ConfigValue
		Value: value,
	}
	return result
}
// TemplateConsortiumName creates a ConfigGroup representing the ConsortiumName
func TemplateConsortium(name string) *ConfigGroup { //SOURCE:cb.ConfigGroup
	return configGroup(ConsortiumKey, MarshalOrPanic(&ConsortiumPROTO{Name: name})) //WAS:Consortium //SOURCE:utils.MarshalOrPanic //SOURCE:cb.Consortium
}
// TemplateHashingAlgorithm creates a ConfigGroup representing the HashingAlgorithm
func TemplateHashingAlgorithm(name string) *ConfigGroup { //SOURCE:cb.ConfigGroup
	return configGroup(HashingAlgorithmKey, MarshalOrPanic(&HashingAlgorithm{Name: name})) //SOURCE:utils.MarshalOrPanic //SOURCE:cb.HashingAlgorithm
}
// DefaultHashingAlgorithm creates a headerless config item for the default hashing algorithm
func DefaultHashingAlgorithm() *ConfigGroup { //SOURCE:cb.ConfigGroup
	return TemplateHashingAlgorithm(defaultHashingAlgorithm)
}
const defaultBlockDataHashingStructureWidth = math.MaxUint32
// TemplateBlockDataHashingStructure creates a headerless config item representing the block data hashing structure
func TemplateBlockDataHashingStructure(width uint32) *ConfigGroup { //SOURCE:cb.ConfigGroup
	return configGroup(BlockDataHashingStructureKey, MarshalOrPanic(&BlockDataHashingStructure{Width: width})) //SOURCE:utils.MarshalOrPanic //SOURCE:cb.BlockDataHashingStructure
}
// DefaultBlockDatahashingStructure creates a headerless config item for the default block data hashing structure
func DefaultBlockDataHashingStructure() *ConfigGroup { //SOURCE:cb.ConfigGroup
	return TemplateBlockDataHashingStructure(defaultBlockDataHashingStructureWidth)
}
// TemplateOrdererAddressess creates a headerless config item representing the orderer addresses
func TemplateOrdererAddresses(addresses []string) *ConfigGroup { //SOURCE:cb.ConfigGroup
	return configGroup(OrdererAddressesKey, MarshalOrPanic(&OrdererAddresses{Addresses: addresses})) //SOURCE:utils.MarshalOrPanic //SOURCE:cb.OrdererAddresses
}

/*** fabric/bccsp/keystore.go ***/
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

/*** fabric/bccsp/bccsp.go ***/
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
// KeyGenOpts contains options for key-generation with a CSP.
type KeyGenOpts interface {
	// Algorithm returns the key generation algorithm identifier (to be used).
	Algorithm() string
	// Ephemeral returns true if the key to generate has to be ephemeral,
	// false otherwise.
	Ephemeral() bool
}
// KeyDerivOpts contains options for key-derivation with a CSP.
type KeyDerivOpts interface {
	// Algorithm returns the key derivation algorithm identifier (to be used).
	Algorithm() string
	// Ephemeral returns true if the key to derived has to be ephemeral,
	// false otherwise.
	Ephemeral() bool
}
// KeyImportOpts contains options for importing the raw material of a key with a CSP.
type KeyImportOpts interface {
	// Algorithm returns the key importation algorithm identifier (to be used).
	Algorithm() string
	// Ephemeral returns true if the key generated has to be ephemeral,
	// false otherwise.
	Ephemeral() bool
}
// HashOpts contains options for hashing with a CSP.
type HashOpts interface {
	// Algorithm returns the hash algorithm identifier (to be used).
	Algorithm() string
}
// SignerOpts contains options for signing with a CSP.
type SignerOpts interface {
	crypto.SignerOpts
}
// EncrypterOpts contains options for encrypting with a CSP.
type EncrypterOpts interface{}
// DecrypterOpts contains options for decrypting with a CSP.
type DecrypterOpts interface{}
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

/*** fabric/bccsp/pkcs11/conf.go ***/
type configPKCS11 struct { //WAS:config
	ellipticCurve asn1.ObjectIdentifier
	hashFunction  func() hash.Hash
	aesBitLength  int
	rsaBitLength  int
}
func (conf *configPKCS11) setSecurityLevel(securityLevel int, hashFamily string) (err error) {
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
func (conf *configPKCS11) setSecurityLevelSHA2(level int) (err error) {
	switch level {
	case 256:
		conf.ellipticCurve = oidNamedCurveP256
		conf.hashFunction = sha256.New
		conf.rsaBitLength = 2048
		conf.aesBitLength = 32
	case 384:
		conf.ellipticCurve = oidNamedCurveP384
		conf.hashFunction = sha512.New384
		conf.rsaBitLength = 3072
		conf.aesBitLength = 32
	default:
		err = fmt.Errorf("Security level not supported [%d]", level)
	}
	return
}
func (conf *configPKCS11) setSecurityLevelSHA3(level int) (err error) {
	switch level {
	case 256:
		conf.ellipticCurve = oidNamedCurveP256
		conf.hashFunction = sha3.New256
		conf.rsaBitLength = 2048
		conf.aesBitLength = 32
	case 384:
		conf.ellipticCurve = oidNamedCurveP384
		conf.hashFunction = sha3.New384
		conf.rsaBitLength = 3072
		conf.aesBitLength = 32
	default:
		err = fmt.Errorf("Security level not supported [%d]", level)
	}
	return
}
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

/*** fabric/bccsp/pkcs11/pkcs11.go ***/
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
func (csp *implPKCS11) getSession() (session pkcs11.SessionHandle) { //WAS:impl
	select {
	case session = <-csp.sessions:
		logger.Debugf("Reusing existing pkcs11 session %+v on slot %d\n", session, csp.slot)
	default:
		// cache is empty (or completely in use), create a new session
		var s pkcs11.SessionHandle
		var err error = nil
		for i := 0; i < 10; i++ {
			s, err = csp.ctx.OpenSession(csp.slot, pkcs11.CKF_SERIAL_SESSION|pkcs11.CKF_RW_SESSION)
			if err != nil {
				logger.Warningf("OpenSession failed, retrying [%s]\n", err)
			} else {
				break
			}
		}
		if err != nil {
			panic(fmt.Errorf("OpenSession failed [%s]\n", err))
		}
		logger.Debugf("Created new pkcs11 session %+v on slot %d\n", s, csp.slot)
		session = s
	}
	return session
}
func (csp *implPKCS11) returnSession(session pkcs11.SessionHandle) { //WAS:impl
	select {
	case csp.sessions <- session:
		// returned session back to session cache
	default:
		// have plenty of sessions in cache, dropping
		csp.ctx.CloseSession(session)
	}
}
// Look for an EC key by SKI, stored in CKA_ID
// This function can probably be addapted for both EC and RSA keys.
func (csp *implPKCS11) getECKey(ski []byte) (pubKey *ecdsa.PublicKey, isPriv bool, err error) { //WAS:impl
	p11lib := csp.ctx
	session := csp.getSession()
	defer csp.returnSession(session)
	isPriv = true
	_, err = findKeyPairFromSKI(p11lib, session, ski, privateKeyFlag)
	if err != nil {
		isPriv = false
		logger.Debugf("Private key not found [%s] for SKI [%s], looking for Public key", err, hex.EncodeToString(ski))
	}
	publicKey, err := findKeyPairFromSKI(p11lib, session, ski, publicKeyFlag)
	if err != nil {
		return nil, false, fmt.Errorf("Public key not found [%s] for SKI [%s]", err, hex.EncodeToString(ski))
	}
	ecpt, marshaledOid, err := ecPoint(p11lib, session, *publicKey)
	if err != nil {
		return nil, false, fmt.Errorf("Public key not found [%s] for SKI [%s]", err, hex.EncodeToString(ski))
	}
	curveOid := new(asn1.ObjectIdentifier)
	_, err = asn1.Unmarshal(marshaledOid, curveOid)
	if err != nil {
		return nil, false, fmt.Errorf("Failed Unmarshaling Curve OID [%s]\n%s", err.Error(), hex.EncodeToString(marshaledOid))
	}
	curve := namedCurveFromOID(*curveOid)
	if curve == nil {
		return nil, false, fmt.Errorf("Cound not recognize Curve from OID")
	}
	x, y := elliptic.Unmarshal(curve, ecpt)
	if x == nil {
		return nil, false, fmt.Errorf("Failed Unmarshaling Public Key")
	}
	pubKey = &ecdsa.PublicKey{Curve: curve, X: x, Y: y}
	return pubKey, isPriv, nil
}
// RFC 5480, 2.1.1.1. Named Curve
//
// secp224r1 OBJECT IDENTIFIER ::= {
//   iso(1) identified-organization(3) certicom(132) curve(0) 33 }
//
// secp256r1 OBJECT IDENTIFIER ::= {
//   iso(1) member-body(2) us(840) ansi-X9-62(10045) curves(3)
//   prime(1) 7 }
//
// secp384r1 OBJECT IDENTIFIER ::= {
//   iso(1) identified-organization(3) certicom(132) curve(0) 34 }
//
// secp521r1 OBJECT IDENTIFIER ::= {
//   iso(1) identified-organization(3) certicom(132) curve(0) 35 }
//
var (
	oidNamedCurveP224 = asn1.ObjectIdentifier{1, 3, 132, 0, 33}
	oidNamedCurveP256 = asn1.ObjectIdentifier{1, 2, 840, 10045, 3, 1, 7}
	oidNamedCurveP384 = asn1.ObjectIdentifier{1, 3, 132, 0, 34}
	oidNamedCurveP521 = asn1.ObjectIdentifier{1, 3, 132, 0, 35}
)
func namedCurveFromOID(oid asn1.ObjectIdentifier) elliptic.Curve {
	switch {
	case oid.Equal(oidNamedCurveP224):
		return elliptic.P224()
	case oid.Equal(oidNamedCurveP256):
		return elliptic.P256()
	case oid.Equal(oidNamedCurveP384):
		return elliptic.P384()
	case oid.Equal(oidNamedCurveP521):
		return elliptic.P521()
	}
	return nil
}
func (csp *implPKCS11) generateECKey(curve asn1.ObjectIdentifier, ephemeral bool) (ski []byte, pubKey *ecdsa.PublicKey, err error) { //WAS:impl
	p11lib := csp.ctx
	session := csp.getSession()
	defer csp.returnSession(session)
	id := nextIDCtr()
	publabel := fmt.Sprintf("BCPUB%s", id.Text(16))
	prvlabel := fmt.Sprintf("BCPRV%s", id.Text(16))
	marshaledOID, err := asn1.Marshal(curve)
	if err != nil {
		return nil, nil, fmt.Errorf("Could not marshal OID [%s]", err.Error())
	}
	pubkey_t := []*pkcs11.Attribute{
		pkcs11.NewAttribute(pkcs11.CKA_KEY_TYPE, pkcs11.CKK_EC),
		pkcs11.NewAttribute(pkcs11.CKA_CLASS, pkcs11.CKO_PUBLIC_KEY),
		pkcs11.NewAttribute(pkcs11.CKA_TOKEN, !ephemeral),
		pkcs11.NewAttribute(pkcs11.CKA_VERIFY, true),
		pkcs11.NewAttribute(pkcs11.CKA_EC_PARAMS, marshaledOID),
		pkcs11.NewAttribute(pkcs11.CKA_PRIVATE, false),
		pkcs11.NewAttribute(pkcs11.CKA_ID, publabel),
		pkcs11.NewAttribute(pkcs11.CKA_LABEL, publabel),
	}
	prvkey_t := []*pkcs11.Attribute{
		pkcs11.NewAttribute(pkcs11.CKA_KEY_TYPE, pkcs11.CKK_EC),
		pkcs11.NewAttribute(pkcs11.CKA_CLASS, pkcs11.CKO_PRIVATE_KEY),
		pkcs11.NewAttribute(pkcs11.CKA_TOKEN, !ephemeral),
		pkcs11.NewAttribute(pkcs11.CKA_PRIVATE, true),
		pkcs11.NewAttribute(pkcs11.CKA_SIGN, true),
		pkcs11.NewAttribute(pkcs11.CKA_ID, prvlabel),
		pkcs11.NewAttribute(pkcs11.CKA_LABEL, prvlabel),
		pkcs11.NewAttribute(pkcs11.CKA_EXTRACTABLE, !csp.noPrivImport),
	}
	pub, prv, err := p11lib.GenerateKeyPair(session,
		[]*pkcs11.Mechanism{pkcs11.NewMechanism(pkcs11.CKM_EC_KEY_PAIR_GEN, nil)},
		pubkey_t, prvkey_t)
	if err != nil {
		return nil, nil, fmt.Errorf("P11: keypair generate failed [%s]\n", err)
	}
	ecpt, _, _ := ecPoint(p11lib, session, pub)
	hash := sha256.Sum256(ecpt)
	ski = hash[:]
	// set CKA_ID of the both keys to SKI(public key) and CKA_LABEL to hex string of SKI
	setski_t := []*pkcs11.Attribute{
		pkcs11.NewAttribute(pkcs11.CKA_ID, ski),
		pkcs11.NewAttribute(pkcs11.CKA_LABEL, hex.EncodeToString(ski)),
	}
	logger.Infof("Generated new P11 key, SKI %x\n", ski)
	err = p11lib.SetAttributeValue(session, pub, setski_t)
	if err != nil {
		return nil, nil, fmt.Errorf("P11: set-ID-to-SKI[public] failed [%s]\n", err)
	}
	err = p11lib.SetAttributeValue(session, prv, setski_t)
	if err != nil {
		return nil, nil, fmt.Errorf("P11: set-ID-to-SKI[private] failed [%s]\n", err)
	}
	nistCurve := namedCurveFromOID(curve)
	if curve == nil {
		return nil, nil, fmt.Errorf("Cound not recognize Curve from OID")
	}
	x, y := elliptic.Unmarshal(nistCurve, ecpt)
	if x == nil {
		return nil, nil, fmt.Errorf("Failed Unmarshaling Public Key")
	}
	pubGoKey := &ecdsa.PublicKey{Curve: nistCurve, X: x, Y: y}
	if logger.IsEnabledFor(logging.DEBUG) {
		listAttrs(p11lib, session, prv)
		listAttrs(p11lib, session, pub)
	}
	return ski, pubGoKey, nil
}
func (csp *implPKCS11) signP11ECDSA(ski []byte, msg []byte) (R, S *big.Int, err error) { //WAS:impl
	p11lib := csp.ctx
	session := csp.getSession()
	defer csp.returnSession(session)
	privateKey, err := findKeyPairFromSKI(p11lib, session, ski, privateKeyFlag)
	if err != nil {
		return nil, nil, fmt.Errorf("Private key not found [%s]\n", err)
	}
	err = p11lib.SignInit(session, []*pkcs11.Mechanism{pkcs11.NewMechanism(pkcs11.CKM_ECDSA, nil)}, *privateKey)
	if err != nil {
		return nil, nil, fmt.Errorf("Sign-initialize  failed [%s]\n", err)
	}
	var sig []byte
	sig, err = p11lib.Sign(session, msg)
	if err != nil {
		return nil, nil, fmt.Errorf("P11: sign failed [%s]\n", err)
	}
	R = new(big.Int)
	S = new(big.Int)
	R.SetBytes(sig[0 : len(sig)/2])
	S.SetBytes(sig[len(sig)/2:])
	return R, S, nil
}
func (csp *implPKCS11) verifyP11ECDSA(ski []byte, msg []byte, R, S *big.Int, byteSize int) (valid bool, err error) { //WAS:impl
	p11lib := csp.ctx
	session := csp.getSession()
	defer csp.returnSession(session)
	logger.Debugf("Verify ECDSA\n")
	publicKey, err := findKeyPairFromSKI(p11lib, session, ski, publicKeyFlag)
	if err != nil {
		return false, fmt.Errorf("Public key not found [%s]\n", err)
	}
	r := R.Bytes()
	s := S.Bytes()
	// Pad front of R and S with Zeroes if needed
	sig := make([]byte, 2*byteSize)
	copy(sig[byteSize-len(r):byteSize], r)
	copy(sig[2*byteSize-len(s):], s)
	err = p11lib.VerifyInit(session, []*pkcs11.Mechanism{pkcs11.NewMechanism(pkcs11.CKM_ECDSA, nil)},
		*publicKey)
	if err != nil {
		return false, fmt.Errorf("PKCS11: Verify-initialize [%s]\n", err)
	}
	err = p11lib.Verify(session, msg, sig)
	if err == pkcs11.Error(pkcs11.CKR_SIGNATURE_INVALID) {
		return false, nil
	}
	if err != nil {
		return false, fmt.Errorf("PKCS11: Verify failed [%s]\n", err)
	}
	return true, nil
}
func (csp *implPKCS11) importECKey(curve asn1.ObjectIdentifier, privKey, ecPt []byte, ephemeral bool, keyType bool) (ski []byte, err error) { //WAS:impl
	p11lib := csp.ctx
	session := csp.getSession()
	defer csp.returnSession(session)
	marshaledOID, err := asn1.Marshal(curve)
	if err != nil {
		return nil, fmt.Errorf("Could not marshal OID [%s]", err.Error())
	}
	var keyTemplate []*pkcs11.Attribute
	if keyType == publicKeyFlag {
		logger.Debug("Importing Public EC Key")
		hash := sha256.Sum256(ecPt)
		ski = hash[:]
		publabel := hex.EncodeToString(ski)
		// Add DER encoding for the CKA_EC_POINT
		ecPt = append([]byte{0x04, byte(len(ecPt))}, ecPt...)
		keyTemplate = []*pkcs11.Attribute{
			pkcs11.NewAttribute(pkcs11.CKA_KEY_TYPE, pkcs11.CKK_EC),
			pkcs11.NewAttribute(pkcs11.CKA_CLASS, pkcs11.CKO_PUBLIC_KEY),
			pkcs11.NewAttribute(pkcs11.CKA_TOKEN, !ephemeral),
			pkcs11.NewAttribute(pkcs11.CKA_VERIFY, true),
			pkcs11.NewAttribute(pkcs11.CKA_EC_PARAMS, marshaledOID),

			pkcs11.NewAttribute(pkcs11.CKA_ID, ski),
			pkcs11.NewAttribute(pkcs11.CKA_LABEL, publabel),
			pkcs11.NewAttribute(pkcs11.CKA_EC_POINT, ecPt),
			pkcs11.NewAttribute(pkcs11.CKA_PRIVATE, false),
		}
	} else { // isPrivateKey
		ski, err = csp.importECKey(curve, nil, ecPt, ephemeral, publicKeyFlag)
		if err != nil {
			return nil, fmt.Errorf("Failed importing private EC Key [%s]\n", err)
		}
		logger.Debugf("Importing Private EC Key [%d]\n%s\n", len(privKey)*8, hex.Dump(privKey))
		prvlabel := hex.EncodeToString(ski)
		keyTemplate = []*pkcs11.Attribute{
			pkcs11.NewAttribute(pkcs11.CKA_KEY_TYPE, pkcs11.CKK_EC),
			pkcs11.NewAttribute(pkcs11.CKA_CLASS, pkcs11.CKO_PRIVATE_KEY),
			pkcs11.NewAttribute(pkcs11.CKA_TOKEN, !ephemeral),
			pkcs11.NewAttribute(pkcs11.CKA_PRIVATE, false),
			pkcs11.NewAttribute(pkcs11.CKA_SIGN, true),
			pkcs11.NewAttribute(pkcs11.CKA_EC_PARAMS, marshaledOID),
			pkcs11.NewAttribute(pkcs11.CKA_ID, ski),
			pkcs11.NewAttribute(pkcs11.CKA_LABEL, prvlabel),
			pkcs11.NewAttribute(pkcs11.CKR_ATTRIBUTE_SENSITIVE, false),
			pkcs11.NewAttribute(pkcs11.CKA_EXTRACTABLE, true),
			pkcs11.NewAttribute(pkcs11.CKA_VALUE, privKey),
		}
	}
	keyHandle, err := p11lib.CreateObject(session, keyTemplate)
	if err != nil {
		return nil, fmt.Errorf("P11: keypair generate failed [%s]\n", err)
	}
	if logger.IsEnabledFor(logging.DEBUG) {
		listAttrs(p11lib, session, keyHandle)
	}
	return ski, nil
}
const (
	privateKeyFlag = true
	publicKeyFlag  = false
)
func findKeyPairFromSKI(mod *pkcs11.Ctx, session pkcs11.SessionHandle, ski []byte, keyType bool) (*pkcs11.ObjectHandle, error) {
	ktype := pkcs11.CKO_PUBLIC_KEY
	if keyType == privateKeyFlag {
		ktype = pkcs11.CKO_PRIVATE_KEY
	}
	template := []*pkcs11.Attribute{
		pkcs11.NewAttribute(pkcs11.CKA_CLASS, ktype),
		pkcs11.NewAttribute(pkcs11.CKA_ID, ski),
	}
	if err := mod.FindObjectsInit(session, template); err != nil {
		return nil, err
	}
	// single session instance, assume one hit only
	objs, _, err := mod.FindObjects(session, 1)
	if err != nil {
		return nil, err
	}
	if err = mod.FindObjectsFinal(session); err != nil {
		return nil, err
	}
	if len(objs) == 0 {
		return nil, fmt.Errorf("Key not found [%s]", hex.Dump(ski))
	}
	return &objs[0], nil
}
// Fairly straightforward EC-point query, other than opencryptoki
// mis-reporting length, including the 04 Tag of the field following
// the SPKI in EP11-returned MACed publickeys:
//
// attr type 385/x181, length 66 b  -- SHOULD be 1+64
// EC point:
// 00000000  04 ce 30 31 6d 5a fd d3  53 2d 54 9a 27 54 d8 7c
// 00000010  d9 80 35 91 09 2d 6f 06  5a 8e e3 cb c0 01 b7 c9
// 00000020  13 5d 70 d4 e5 62 f2 1b  10 93 f7 d5 77 41 ba 9d
// 00000030  93 3e 18 3e 00 c6 0a 0e  d2 36 cc 7f be 50 16 ef
// 00000040  06 04
//
// cf. correct field:
//   0  89: SEQUENCE {
//   2  19:   SEQUENCE {
//   4   7:     OBJECT IDENTIFIER ecPublicKey (1 2 840 10045 2 1)
//  13   8:     OBJECT IDENTIFIER prime256v1 (1 2 840 10045 3 1 7)
//        :     }
//  23  66:   BIT STRING
//        :     04 CE 30 31 6D 5A FD D3 53 2D 54 9A 27 54 D8 7C
//        :     D9 80 35 91 09 2D 6F 06 5A 8E E3 CB C0 01 B7 C9
//        :     13 5D 70 D4 E5 62 F2 1B 10 93 F7 D5 77 41 BA 9D
//        :     93 3E 18 3E 00 C6 0A 0E D2 36 CC 7F BE 50 16 EF
//        :     06
//        :   }
//
// as a short-term workaround, remove the trailing byte if:
//   - receiving an even number of bytes == 2*prime-coordinate +2 bytes
//   - starting byte is 04: uncompressed EC point
//   - trailing byte is 04: assume it belongs to the next OCTET STRING
//
// [mis-parsing encountered with v3.5.1, 2016-10-22]
//
// SoftHSM reports extra two bytes before the uncrompressed point
// 0x04 || <Length*2+1>
//                 VV< Actual start of point
// 00000000  04 41 04 6c c8 57 32 13  02 12 6a 19 23 1d 5a 64  |.A.l.W2...j.#.Zd|
// 00000010  33 0c eb 75 4d e8 99 22  92 35 96 b2 39 58 14 1e  |3..uM..".5..9X..|
// 00000020  19 de ef 32 46 50 68 02  24 62 36 db ed b1 84 7b  |...2FPh.$b6....{|
// 00000030  93 d8 40 c3 d5 a6 b7 38  16 d2 35 0a 53 11 f9 51  |..@....8..5.S..Q|
// 00000040  fc a7 16                                          |...|
func ecPoint(p11lib *pkcs11.Ctx, session pkcs11.SessionHandle, key pkcs11.ObjectHandle) (ecpt, oid []byte, err error) {
	template := []*pkcs11.Attribute{
		pkcs11.NewAttribute(pkcs11.CKA_EC_POINT, nil),
		pkcs11.NewAttribute(pkcs11.CKA_EC_PARAMS, nil),
	}
	attr, err := p11lib.GetAttributeValue(session, key, template)
	if err != nil {
		return nil, nil, fmt.Errorf("PKCS11: get(EC point) [%s]\n", err)
	}
	for _, a := range attr {
		if a.Type == pkcs11.CKA_EC_POINT {
			logger.Debugf("EC point: attr type %d/0x%x, len %d\n%s\n", a.Type, a.Type, len(a.Value), hex.Dump(a.Value))
			// workarounds, see above
			if (0 == (len(a.Value) % 2)) &&
				(byte(0x04) == a.Value[0]) &&
				(byte(0x04) == a.Value[len(a.Value)-1]) {
				logger.Debugf("Detected opencryptoki bug, trimming trailing 0x04")
				ecpt = a.Value[0 : len(a.Value)-1] // Trim trailing 0x04
			} else if byte(0x04) == a.Value[0] && byte(0x04) == a.Value[2] {
				logger.Debugf("Detected SoftHSM bug, trimming leading 0x04 0xXX")
				ecpt = a.Value[2:len(a.Value)]
			} else {
				ecpt = a.Value
			}
		} else if a.Type == pkcs11.CKA_EC_PARAMS {
			logger.Debugf("EC point: attr type %d/0x%x, len %d\n%s\n", a.Type, a.Type, len(a.Value), hex.Dump(a.Value))
			oid = a.Value
		}
	}
	if oid == nil || ecpt == nil {
		return nil, nil, fmt.Errorf("CKA_EC_POINT not found, perhaps not an EC Key?")
	}
	return ecpt, oid, nil
}
func listAttrs(p11lib *pkcs11.Ctx, session pkcs11.SessionHandle, obj pkcs11.ObjectHandle) {
	var cktype, ckclass uint
	var ckaid, cklabel []byte
	if p11lib == nil {
		return
	}
	template := []*pkcs11.Attribute{
		pkcs11.NewAttribute(pkcs11.CKA_CLASS, ckclass),
		pkcs11.NewAttribute(pkcs11.CKA_KEY_TYPE, cktype),
		pkcs11.NewAttribute(pkcs11.CKA_ID, ckaid),
		pkcs11.NewAttribute(pkcs11.CKA_LABEL, cklabel),
	}
	// certain errors are tolerated, if value is missing
	attr, err := p11lib.GetAttributeValue(session, obj, template)
	if err != nil {
		logger.Debugf("P11: get(attrlist) [%s]\n", err)
	}
	for _, a := range attr {
		// Would be friendlier if the bindings provided a way convert Attribute hex to string
		logger.Debugf("ListAttr: type %d/0x%x, length %d\n%s", a.Type, a.Type, len(a.Value), hex.Dump(a.Value))
	}
}
func (csp *implPKCS11) getSecretValue(ski []byte) []byte { //WAS:impl
	p11lib := csp.ctx
	session := csp.getSession()
	defer csp.returnSession(session)
	keyHandle, err := findKeyPairFromSKI(p11lib, session, ski, privateKeyFlag)
	var privKey []byte
	template := []*pkcs11.Attribute{
		pkcs11.NewAttribute(pkcs11.CKA_VALUE, privKey),
	}
	// certain errors are tolerated, if value is missing
	attr, err := p11lib.GetAttributeValue(session, *keyHandle, template)
	if err != nil {
		logger.Warningf("P11: get(attrlist) [%s]\n", err)
	}
	for _, a := range attr {
		// Would be friendlier if the bindings provided a way convert Attribute hex to string
		logger.Debugf("ListAttr: type %d/0x%x, length %d\n%s", a.Type, a.Type, len(a.Value), hex.Dump(a.Value))
		return a.Value
	}
	logger.Warningf("No Key Value found!", err)
	return nil
}
var (
	bigone   = new(big.Int).SetInt64(1)
	id_ctr   = new(big.Int)
	id_mutex sync.Mutex
)
func nextIDCtr() *big.Int {
	id_mutex.Lock()
	id_ctr = new(big.Int).Add(id_ctr, bigone)
	id_mutex.Unlock()
	return id_ctr
}

/*** fabric/bccsp/pkcs11/ecdsa.go ***/
type ecdsaSignaturePKCS11 struct { //WAS:ecdsaSignature
	R, S *big.Int
}
func marshalECDSASignature(r, s *big.Int) ([]byte, error) {
	return asn1.Marshal(ecdsaSignaturePKCS11{r, s})  //WAS:ecdsaSignature
}
func unmarshalECDSASignature(raw []byte) (*big.Int, *big.Int, error) {
	// Unmarshal
	sig := new(ecdsaSignaturePKCS11)  //WAS:ecdsaSignature
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
func (csp *implPKCS11) signECDSA(k ecdsaPrivateKeyPKCS11, digest []byte, opts SignerOpts) (signature []byte, err error) { //WAS:impl //WAS:ecdsaPrivateKey //SOURCE:bccsp.SignerOpts
	r, s, err := csp.signP11ECDSA(k.ski, digest)
	if err != nil {
		return nil, err
	}
	// check for low-S
	halfOrder, ok := curveHalfOrders[k.pub.pub.Curve]
	if !ok {
		return nil, fmt.Errorf("Curve not recognized [%s]", k.pub.pub.Curve)
	}
	// is s > halfOrder Then
	if s.Cmp(halfOrder) == 1 {
		// Set s to N - s that will be then in the lower part of signature space
		// less or equal to half order
		s.Sub(k.pub.pub.Params().N, s)
	}
	return marshalECDSASignature(r, s)
}
func (csp *implPKCS11) verifyECDSA(k ecdsaPublicKeyPKCS11, signature, digest []byte, opts SignerOpts) (valid bool, err error) { //WAS:impl //WAS:ecdsaPublicKey //SOURCE:bccsp.SignerOpts
	r, s, err := unmarshalECDSASignature(signature)
	if err != nil {
		return false, fmt.Errorf("Failed unmashalling signature [%s]", err)
	}
	// check for low-S
	halfOrder, ok := curveHalfOrders[k.pub.Curve]
	if !ok {
		return false, fmt.Errorf("Curve not recognized [%s]", k.pub.Curve)
	}
	// If s > halfOrder Then
	if s.Cmp(halfOrder) == 1 {
		return false, fmt.Errorf("Invalid S. Must be smaller than half the order [%s][%s].", s, halfOrder)
	}
	if csp.softVerify {
		return ecdsa.Verify(k.pub, digest, r, s), nil
	} else {
		return csp.verifyP11ECDSA(k.ski, digest, r, s, k.pub.Curve.Params().BitSize/8)
	}
}

/*** fabric/bccsp/pkcs11/ecdsakey.go ***/
type ecdsaPrivateKeyPKCS11 struct { //WAS:ecdsaPrivateKey
	ski []byte
	pub ecdsaPublicKeyPKCS11 //WAS:ecdsaPublicKey
}
// Bytes converts this key to its byte representation,
// if this operation is allowed.
func (k *ecdsaPrivateKeyPKCS11) Bytes() (raw []byte, err error) { //WAS:ecdsaPrivateKey
	return nil, errors.New("Not supported.")
}
// SKI returns the subject key identifier of this key.
func (k *ecdsaPrivateKeyPKCS11) SKI() (ski []byte) { //WAS:ecdsaPrivateKey
	return k.ski
}
// Symmetric returns true if this key is a symmetric key,
// false if this key is asymmetric
func (k *ecdsaPrivateKeyPKCS11) Symmetric() bool { //WAS:ecdsaPrivateKey
	return false
}
// Private returns true if this key is a private key,
// false otherwise.
func (k *ecdsaPrivateKeyPKCS11) Private() bool { //WAS:ecdsaPrivateKey
	return true
}
// PublicKey returns the corresponding public key part of an asymmetric public/private key pair.
// This method returns an error in symmetric key schemes.
func (k *ecdsaPrivateKeyPKCS11) PublicKey() (Key, error) { //WAS:ecdsaPrivateKey //SOURCE:bccsp.Key
	return &k.pub, nil
}
type ecdsaPublicKeyPKCS11 struct { //WAS:ecdsaPublicKey
	ski []byte
	pub *ecdsa.PublicKey
}
// Bytes converts this key to its byte representation,
// if this operation is allowed.
func (k *ecdsaPublicKeyPKCS11) Bytes() (raw []byte, err error) { //WAS:ecdsaPublicKey
	raw, err = x509.MarshalPKIXPublicKey(k.pub)
	if err != nil {
		return nil, fmt.Errorf("Failed marshalling key [%s]", err)
	}
	return
}
// SKI returns the subject key identifier of this key.
func (k *ecdsaPublicKeyPKCS11) SKI() (ski []byte) { //WAS:ecdsaPublicKey
	return k.ski
}
// Symmetric returns true if this key is a symmetric key,
// false if this key is asymmetric
func (k *ecdsaPublicKeyPKCS11) Symmetric() bool { //WAS:ecdsaPublicKey
	return false
}
// Private returns true if this key is a private key,
// false otherwise.
func (k *ecdsaPublicKeyPKCS11) Private() bool { //WAS:ecdsaPublicKey
	return false
}
// PublicKey returns the corresponding public key part of an asymmetric public/private key pair.
// This method returns an error in symmetric key schemes.
func (k *ecdsaPublicKeyPKCS11) PublicKey() (Key, error) { //WAS:ecdsaPublicKey //SOURCE:bccsp.Key
	return k, nil
}

/*** fabric/bccsp/pkcs11/impl.go ***/
var sessionCacheSize = 10
// New returns a new instance of the software-based BCCSP
// set at the passed security level, hash family and KeyStore.
func NewPKCS11(opts PKCS11Opts, keyStore KeyStore) (BCCSP, error) { //WAS:New //SOURCE:bccsp.KeyStore //SOURCE:bccsp.BCCSP
	// Init config
	conf := &configPKCS11{}
	err := conf.setSecurityLevel(opts.SecLevel, opts.HashFamily)
	if err != nil {
		return nil, fmt.Errorf("Failed initializing configuration [%s]", err)
	}
	swCSP, err := NewSW(opts.SecLevel, opts.HashFamily, keyStore) //WAS:New //SOURCE:sw.New
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
	csp := &implPKCS11{swCSP, conf, keyStore, ctx, sessions, slot, lib, opts.Sensitive, opts.SoftVerify} //WAS:impl
	csp.returnSession(*session)
	return csp, nil
}
type implPKCS11 struct { //WAS:impl
	BCCSP //SOURCE:bccsp.BCCSP
	conf *configPKCS11 //WAS:config
	ks   KeyStore //SOURCE:bccsp.KeyStore
	ctx      *pkcs11.Ctx
	sessions chan pkcs11.SessionHandle
	slot     uint
	lib          string
	noPrivImport bool
	softVerify   bool
}
// KeyGen generates a key using opts.
func (csp *implPKCS11) KeyGenPKCS11(opts KeyGenOpts) (k Key, err error) { //WAS:impl //WAS:KeyGen //SOURCE:bccsp.KeyGenOpts //SOURCE:bccsp.Key
	// Validate arguments
	if opts == nil {
		return nil, errors.New("Invalid Opts parameter. It must not be nil.")
	}
	// Parse algorithm
	switch opts.(type) {
	case *ECDSAKeyGenOpts: //SOURCE:bccsp.ECDSAKeyGenOpts
		ski, pub, err := csp.generateECKey(csp.conf.ellipticCurve, opts.Ephemeral())
		if err != nil {
			return nil, fmt.Errorf("Failed generating ECDSA key [%s]", err)
		}
		k = &ecdsaPrivateKeyPKCS11{ski, ecdsaPublicKeyPKCS11{ski, pub}} //WAS:ecdsaPrivatecKey //WAS:ecdsaPublicKey

	case *ECDSAP256KeyGenOpts: //SOURCE:bccsp.ECDSAP256KeyGenOpts
		ski, pub, err := csp.generateECKey(oidNamedCurveP256, opts.Ephemeral())
		if err != nil {
			return nil, fmt.Errorf("Failed generating ECDSA P256 key [%s]", err)
		}
		k = &ecdsaPrivateKeyPKCS11{ski, ecdsaPublicKeyPKCS11{ski, pub}} //WAS:ecdsaPrivatecKey //WAS:ecdsaPublicKey

	case *ECDSAP384KeyGenOpts: //SOURCE:bccsp.ECDSAP384KeyGenOpts
		ski, pub, err := csp.generateECKey(oidNamedCurveP384, opts.Ephemeral())
		if err != nil {
			return nil, fmt.Errorf("Failed generating ECDSA P384 key [%s]", err)
		}
		k = &ecdsaPrivateKeyPKCS11{ski, ecdsaPublicKeyPKCS11{ski, pub}} //WAS:ecdsaPrivatecKey //WAS:ecdsaPublicKey
	default:
		return csp.BCCSP.KeyGen(opts)
	}
	return k, nil
}
// KeyDeriv derives a key from k using opts.
// The opts argument should be appropriate for the primitive used.
func (csp *implPKCS11) KeyDeriv(k Key, opts KeyDerivOpts) (dk Key, err error) { //WAS:impl //SOURCE:bccsp.Key //SOURCE:bccsp.KeyDerivOpts
	// Validate arguments
	if k == nil {
		return nil, errors.New("Invalid Key. It must not be nil.")
	}
	// Derive key
	switch k.(type) {
	case *ecdsaPublicKeyPKCS11: //WAS:ecdsaPublicKey
		// Validate opts
		if opts == nil {
			return nil, errors.New("Invalid Opts parameter. It must not be nil.")
		}
		ecdsaK := k.(*ecdsaPublicKeyPKCS11) //WAS:ecdsaPublicKey
		switch opts.(type) {
		// Re-randomized an ECDSA public key
		case *ECDSAReRandKeyOpts: //SOURCE:bccsp.ECDSAReRandKeyOpts
			pubKey := ecdsaK.pub
			if pubKey == nil {
				return nil, errors.New("Public base key cannot be nil.")
			}
			reRandOpts := opts.(*ECDSAReRandKeyOpts) //SOURCE:bccsp.ECDSAReRandKeyOpts
			tempSK := &ecdsa.PublicKey{
				Curve: pubKey.Curve,
				X:     new(big.Int),
				Y:     new(big.Int),
			}
			var k = new(big.Int).SetBytes(reRandOpts.ExpansionValue())
			var one = new(big.Int).SetInt64(1)
			n := new(big.Int).Sub(pubKey.Params().N, one)
			k.Mod(k, n)
			k.Add(k, one)
			// Compute temporary public key
			tempX, tempY := pubKey.ScalarBaseMult(k.Bytes())
			tempSK.X, tempSK.Y = tempSK.Add(
				pubKey.X, pubKey.Y,
				tempX, tempY,
			)
			// Verify temporary public key is a valid point on the reference curve
			isOn := tempSK.Curve.IsOnCurve(tempSK.X, tempSK.Y)
			if !isOn {
				return nil, errors.New("Failed temporary public key IsOnCurve check.")
			}
			ecPt := elliptic.Marshal(tempSK.Curve, tempSK.X, tempSK.Y)
			oid, ok := oidFromNamedCurve(tempSK.Curve)
			if !ok {
				return nil, errors.New("Do not know OID for this Curve.")
			}
			ski, err := csp.importECKey(oid, nil, ecPt, opts.Ephemeral(), publicKeyFlag)
			if err != nil {
				return nil, fmt.Errorf("Failed getting importing EC Public Key [%s]", err)
			}
			reRandomizedKey := &ecdsaPublicKeyPKCS11{ski, tempSK} //WAS:ecdsaPublicKey
			return reRandomizedKey, nil
		default:
			return nil, fmt.Errorf("Unrecognized KeyDerivOpts provided [%s]", opts.Algorithm())
		}
	case *ecdsaPrivateKeyPKCS11: //WAS:ecdsaPrivatecKey
		// Validate opts
		if opts == nil {
			return nil, errors.New("Invalid Opts parameter. It must not be nil.")
		}
		ecdsaK := k.(*ecdsaPrivateKeyPKCS11) //WAS:ecdsaPrivatecKey
		switch opts.(type) {
		// Re-randomized an ECDSA private key
		case *ECDSAReRandKeyOpts: //SOURCE:bccsp.ECDSAReRandKeyOpts
			reRandOpts := opts.(*ECDSAReRandKeyOpts) //SOURCE:bccsp.ECDSAReRandKeyOpts
			pubKey := ecdsaK.pub.pub
			if pubKey == nil {
				return nil, errors.New("Public base key cannot be nil.")
			}
			secret := csp.getSecretValue(ecdsaK.ski)
			if secret == nil {
				return nil, errors.New("Could not obtain EC Private Key")
			}
			bigSecret := new(big.Int).SetBytes(secret)
			tempSK := &ecdsa.PrivateKey{
				PublicKey: ecdsa.PublicKey{
					Curve: pubKey.Curve,
					X:     new(big.Int),
					Y:     new(big.Int),
				},
				D: new(big.Int),
			}
			var k = new(big.Int).SetBytes(reRandOpts.ExpansionValue())
			var one = new(big.Int).SetInt64(1)
			n := new(big.Int).Sub(pubKey.Params().N, one)
			k.Mod(k, n)
			k.Add(k, one)
			tempSK.D.Add(bigSecret, k)
			tempSK.D.Mod(tempSK.D, pubKey.Params().N)
			// Compute temporary public key
			tempSK.PublicKey.X, tempSK.PublicKey.Y = pubKey.ScalarBaseMult(tempSK.D.Bytes())
			// Verify temporary public key is a valid point on the reference curve
			isOn := tempSK.Curve.IsOnCurve(tempSK.PublicKey.X, tempSK.PublicKey.Y)
			if !isOn {
				return nil, errors.New("Failed temporary public key IsOnCurve check.")
			}
			ecPt := elliptic.Marshal(tempSK.Curve, tempSK.X, tempSK.Y)
			oid, ok := oidFromNamedCurve(tempSK.Curve)
			if !ok {
				return nil, errors.New("Do not know OID for this Curve.")
			}
			ski, err := csp.importECKey(oid, tempSK.D.Bytes(), ecPt, opts.Ephemeral(), privateKeyFlag)
			if err != nil {
				return nil, fmt.Errorf("Failed getting importing EC Public Key [%s]", err)
			}
			reRandomizedKey := &ecdsaPrivateKeyPKCS11{ski, ecdsaPublicKeyPKCS11{ski, &tempSK.PublicKey}} //WAS:ecdsaPrivatecKey //WAS:ecdsaPublicKey
			return reRandomizedKey, nil
		default:
			return nil, fmt.Errorf("Unrecognized KeyDerivOpts provided [%s]", opts.Algorithm())
		}
	default:
		return csp.BCCSP.KeyDeriv(k, opts)
	}
}
// KeyImport imports a key from its raw representation using opts.
// The opts argument should be appropriate for the primitive used.
func (csp *implPKCS11) KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error) { //WAS:impl //SOURCE:bccsp.KeyImportOpts //SOURCE:bccsp.Key
	// Validate arguments
	if raw == nil {
		return nil, errors.New("Invalid raw. Cannot be nil.")
	}
	if opts == nil {
		return nil, errors.New("Invalid Opts parameter. It must not be nil.")
	}
	switch opts.(type) {

	case *ECDSAPKIXPublicKeyImportOpts: //SOURCE:bccsp.ECDSAPKIXPublicKeyImportOpts
		der, ok := raw.([]byte)
		if !ok {
			return nil, errors.New("[ECDSAPKIXPublicKeyImportOpts] Invalid raw material. Expected byte array.")
		}
		if len(der) == 0 {
			return nil, errors.New("[ECDSAPKIXPublicKeyImportOpts] Invalid raw. It must not be nil.")
		}
		lowLevelKey, err := DERToPublicKey(der)  //SOURCE:utils.DERToPublicKey
		if err != nil {
			return nil, fmt.Errorf("Failed converting PKIX to ECDSA public key [%s]", err)
		}
		ecdsaPK, ok := lowLevelKey.(*ecdsa.PublicKey)
		if !ok {
			return nil, errors.New("Failed casting to ECDSA public key. Invalid raw material.")
		}
		ecPt := elliptic.Marshal(ecdsaPK.Curve, ecdsaPK.X, ecdsaPK.Y)
		oid, ok := oidFromNamedCurve(ecdsaPK.Curve)
		if !ok {
			return nil, errors.New("Do not know OID for this Curve.")
		}
		var ski []byte
		if csp.noPrivImport {
			// opencryptoki does not support public ec key imports. This is a sufficient
			// workaround for now to use soft verify
			hash := sha256.Sum256(ecPt)
			ski = hash[:]
		} else {
			// Warn about potential future problems
			if !csp.softVerify {
				logger.Debugf("opencryptoki workaround warning: Importing public EC Key does not store out to pkcs11 store,\n" +
					"so verify with this key will fail, unless key is already present in store. Enable 'softwareverify'\n" +
					"in pkcs11 options, if suspect this issue.")
			}
			ski, err = csp.importECKey(oid, nil, ecPt, opts.Ephemeral(), publicKeyFlag)
			if err != nil {
				return nil, fmt.Errorf("Failed getting importing EC Public Key [%s]", err)
			}
		}
		k = &ecdsaPublicKeyPKCS11{ski, ecdsaPK} //WAS:ecdsaPublicKey
		return k, nil

	case *ECDSAPrivateKeyImportOpts: //SOURCE:bccsp.ECDSAPrivateKeyImportOpts
		if csp.noPrivImport {
			return nil, errors.New("[ECDSADERPrivateKeyImportOpts] PKCS11 options 'sensitivekeys' is set to true. Cannot import.")
		}
		der, ok := raw.([]byte)
		if !ok {
			return nil, errors.New("[ECDSADERPrivateKeyImportOpts] Invalid raw material. Expected byte array.")
		}
		if len(der) == 0 {
			return nil, errors.New("[ECDSADERPrivateKeyImportOpts] Invalid raw. It must not be nil.")
		}
		lowLevelKey, err := DERToPrivateKey(der) //SOURCE:utils.DERToPublicKey
		if err != nil {
			return nil, fmt.Errorf("Failed converting PKIX to ECDSA public key [%s]", err)
		}
		ecdsaSK, ok := lowLevelKey.(*ecdsa.PrivateKey)
		if !ok {
			return nil, errors.New("Failed casting to ECDSA public key. Invalid raw material.")
		}
		ecPt := elliptic.Marshal(ecdsaSK.Curve, ecdsaSK.X, ecdsaSK.Y)
		oid, ok := oidFromNamedCurve(ecdsaSK.Curve)
		if !ok {
			return nil, errors.New("Do not know OID for this Curve.")
		}
		ski, err := csp.importECKey(oid, ecdsaSK.D.Bytes(), ecPt, opts.Ephemeral(), privateKeyFlag)
		if err != nil {
			return nil, fmt.Errorf("Failed getting importing EC Private Key [%s]", err)
		}
		k = &ecdsaPrivateKeyPKCS11{ski, ecdsaPublicKeyPKCS11{ski, &ecdsaSK.PublicKey}} //WAS:ecdsaPrivatecKey //WAS:ecdsaPublicKey
		return k, nil

	case *ECDSAGoPublicKeyImportOpts: //SOURCE:bccsp.ECDSAGoPublicKeyImportOpts
		lowLevelKey, ok := raw.(*ecdsa.PublicKey)
		if !ok {
			return nil, errors.New("[ECDSAGoPublicKeyImportOpts] Invalid raw material. Expected *ecdsa.PublicKey.")
		}
		ecPt := elliptic.Marshal(lowLevelKey.Curve, lowLevelKey.X, lowLevelKey.Y)
		oid, ok := oidFromNamedCurve(lowLevelKey.Curve)
		if !ok {
			return nil, errors.New("Do not know OID for this Curve.")
		}
		var ski []byte
		if csp.noPrivImport {
			// opencryptoki does not support public ec key imports. This is a sufficient
			// workaround for now to use soft verify
			hash := sha256.Sum256(ecPt)
			ski = hash[:]
		} else {
			// Warn about potential future problems
			if !csp.softVerify {
				logger.Debugf("opencryptoki workaround warning: Importing public EC Key does not store out to pkcs11 store,\n" +
					"so verify with this key will fail, unless key is already present in store. Enable 'softwareverify'\n" +
					"in pkcs11 options, if suspect this issue.")
			}
			ski, err = csp.importECKey(oid, nil, ecPt, opts.Ephemeral(), publicKeyFlag)
			if err != nil {
				return nil, fmt.Errorf("Failed getting importing EC Public Key [%s]", err)
			}
		}
		k = &ecdsaPublicKeyPKCS11{ski, lowLevelKey} //WAS:ecdsaPublicKey
		return k, nil
	case *X509PublicKeyImportOpts: //SOURCE:bccsp.X509PublicKeyImportOpts
		x509Cert, ok := raw.(*x509.Certificate)
		if !ok {
			return nil, errors.New("[X509PublicKeyImportOpts] Invalid raw material. Expected *x509.Certificate.")
		}
		pk := x509Cert.PublicKey
		switch pk.(type) {
		case *ecdsa.PublicKey:
			return csp.KeyImport(pk, &ECDSAGoPublicKeyImportOpts{Temporary: opts.Ephemeral()}) //SOURCE:bccsp.ECDSAGoPublicKeyImportOpts
		case *rsa.PublicKey:
			return csp.KeyImport(pk, &RSAGoPublicKeyImportOpts{Temporary: opts.Ephemeral()}) //SOURCE:bccsp.RSAGoPublicKeyImportOpts
		default:
			return nil, errors.New("Certificate's public key type not recognized. Supported keys: [ECDSA, RSA]")
		}
	default:
		return csp.BCCSP.KeyImport(raw, opts)
	}
}
// GetKey returns the key this CSP associates to
// the Subject Key Identifier ski.
func (csp *implPKCS11) GetKey(ski []byte) (k Key, err error) { //WAS:impl //SOURCE:bccsp.Key
	pubKey, isPriv, err := csp.getECKey(ski)
	if err == nil {
		if isPriv {
			return &ecdsaPrivateKeyPKCS11{ski, ecdsaPublicKeyPKCS11{ski, pubKey}}, nil //WAS:ecdsaPrivatecKey //WAS:ecdsaPublicKey
		} else {
			return &ecdsaPublicKeyPKCS11{ski, pubKey}, nil //WAS:ecdsaPublicKey
		}
	}
	return csp.BCCSP.GetKey(ski)
}
// Sign signs digest using key k.
// The opts argument should be appropriate for the primitive used.
// Note that when a signature of a hash of a larger message is needed,
// the caller is responsible for hashing the larger message and passing
// the hash (as digest).
func (csp *implPKCS11) Sign(k Key, digest []byte, opts SignerOpts) (signature []byte, err error) { //WAS:impl //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	// Validate arguments
	if k == nil {
		return nil, errors.New("Invalid Key. It must not be nil.")
	}
	if len(digest) == 0 {
		return nil, errors.New("Invalid digest. Cannot be empty.")
	}
	// Check key type
	switch k.(type) {
	case *ecdsaPrivateKeyPKCS11: //WAS:ecdsaPrivatecKey
		return csp.signECDSA(*k.(*ecdsaPrivateKeyPKCS11), digest, opts) //WAS:ecdsaPrivatecKey
	default:
		return csp.BCCSP.Sign(k, digest, opts)
	}
}
// Verify verifies signature against key k and digest
func (csp *implPKCS11) Verify(k Key, signature, digest []byte, opts SignerOpts) (valid bool, err error) { //WAS:impl //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	// Validate arguments
	if k == nil {
		return false, errors.New("Invalid Key. It must not be nil.")
	}
	if len(signature) == 0 {
		return false, errors.New("Invalid signature. Cannot be empty.")
	}
	if len(digest) == 0 {
		return false, errors.New("Invalid digest. Cannot be empty.")
	}
	// Check key type
	switch k.(type) {
	case *ecdsaPrivateKeyPKCS11: //WAS:ecdsaPrivatecKey
		return csp.verifyECDSA(k.(*ecdsaPrivateKeyPKCS11).pub, signature, digest, opts) //WAS:ecdsaPrivatecKey
	case *ecdsaPublicKeyPKCS11: //WAS:ecdsaPublicKey
		return csp.verifyECDSA(*k.(*ecdsaPublicKeyPKCS11), signature, digest, opts) //WAS:ecdsaPublicKey
	default:
		return csp.BCCSP.Verify(k, signature, digest, opts)
	}
}
// Encrypt encrypts plaintext using key k.
// The opts argument should be appropriate for the primitive used.
func (csp *implPKCS11) Encrypt(k Key, plaintext []byte, opts EncrypterOpts) (ciphertext []byte, err error) { //WAS:impl //SOURCE:bccsp.Key //SOURCE:bccsp.EncrypterOpts
	// TODO: Add PKCS11 support for encryption, when fabric starts requiring it
	return csp.BCCSP.Encrypt(k, plaintext, opts)
}
// Decrypt decrypts ciphertext using key k.
// The opts argument should be appropriate for the primitive used.
func (csp *implPKCS11) Decrypt(k Key, ciphertext []byte, opts DecrypterOpts) (plaintext []byte, err error) { //WAS:impl //SOURCE:bccsp.Key //SOURCE:bccsp.DecrypterOpts
	return csp.BCCSP.Decrypt(k, ciphertext, opts)
}

/*** fabric/bccsp/factory/pkcs11factory.go ***/
const (
	// PKCS11BasedFactoryName is the name of the factory of the hsm-based BCCSP implementation
	PKCS11BasedFactoryName = "PKCS11"
)
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
	return NewPKCS11(*p11Opts, ks) //WAS:New //SOURCE:pkcs11.New
}

/*** fabric/bccsp/factory/opts.go ***/
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

/*** fabric/bccsp/factory/pkcs11.go ***/
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

/*** fabric/bccsp/sw/dummyks.go ***/
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

/*** fabric/bccsp/utils/slice.go ***/
// Clone clones the passed slice
func Clone(src []byte) []byte {
	clone := make([]byte, len(src))
	copy(clone, src)
	return clone
}

/*** fabric/bccsp/utils/keys.go ***/
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
// PrivateKeyToDER marshals a private key to der
func PrivateKeyToDER(privateKey *ecdsa.PrivateKey) ([]byte, error) {
	if privateKey == nil {
		return nil, errors.New("Invalid ecdsa private key. It must be different from nil.")
	}
	return x509.MarshalECPrivateKey(privateKey)
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
// PublicKeyToDER marshals a public key to the der format
func PublicKeyToDER(publicKey interface{}) ([]byte, error) {
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
		return PubASN1, nil
	case *rsa.PublicKey:
		if k == nil {
			return nil, errors.New("Invalid rsa public key. It must be different from nil.")
		}
		PubASN1, err := x509.MarshalPKIXPublicKey(k)
		if err != nil {
			return nil, err
		}
		return PubASN1, nil
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
// DERToPublicKey unmarshals a der to public key
func DERToPublicKey(raw []byte) (pub interface{}, err error) {
	if len(raw) == 0 {
		return nil, errors.New("Invalid DER. It must be different from nil.")
	}
	key, err := x509.ParsePKIXPublicKey(raw)
	return key, err
}

/*** fabric/bccsp/sw/aeskey.go ***/
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

/*** fabric/bccsp/sw/ecdsa.go ***/
type ECDSASignature struct {
	R, S *big.Int
}
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
func SignatureToLowS(k *ecdsa.PublicKey, signature []byte) ([]byte, error) {
	r, s, err := UnmarshalECDSASignature(signature)
	if err != nil {
		return nil, err
	}
	s, modified, err := ToLowS(k, s)
	if err != nil {
		return nil, err
	}
	if modified {
		return MarshalECDSASignature(r, s)
	}
	return signature, nil
}
// IsLow checks that s is a low-S
func IsLowS(k *ecdsa.PublicKey, s *big.Int) (bool, error) {
	halfOrder, ok := curveHalfOrders[k.Curve]
	if !ok {
		return false, fmt.Errorf("Curve not recognized [%s]", k.Curve)
	}
	return s.Cmp(halfOrder) != 1, nil

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
type ecdsaSigner struct{}
func (s *ecdsaSigner) Sign(k Key, digest []byte, opts SignerOpts) (signature []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	return signECDSA(k.(*ecdsaPrivateKey).privKey, digest, opts)
}
type ecdsaPrivateKeyVerifier struct{}
func (v *ecdsaPrivateKeyVerifier) Verify(k Key, signature, digest []byte, opts SignerOpts) (valid bool, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	return verifyECDSA(&(k.(*ecdsaPrivateKey).privKey.PublicKey), signature, digest, opts)
}
type ecdsaPublicKeyKeyVerifier struct{}
func (v *ecdsaPublicKeyKeyVerifier) Verify(k Key, signature, digest []byte, opts SignerOpts) (valid bool, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	return verifyECDSA(k.(*ecdsaPublicKey).pubKey, signature, digest, opts)
}

/*** fabric/bccsp/sw/ecdsakey.go ***/
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

/*** fabric/bccsp/sw/rsa.go ***/
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

/*** fabric/bccsp/sw/rsakey.go ***/
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

/*** fabric/bccsp/utils/io.go ***/
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

/*** fabric/bccsp/utils/errs.go ***/
// ErrToString converts and error to a string. If the error is nil, it returns the string "<clean>"
func ErrToString(err error) string {
	if err != nil {
		return err.Error()
	}
	return "<clean>"
}

/*** fabric/bccsp/sw/conf.go ***/
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

/*** fabric/bccsp/sw/internals.go ***/
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

/*** fabric/common/errors/codes.go ***/
const (
	// Invalid inputs on API calls
	BadRequest = "400"
	// Forbidden due to access control issues
	Forbidden = "403"
	// Not Found (eg chaincode not found)
	NotFound = "404"
	// Request timeout (chaincode or ledger)
	Timeout = "408"
	// Example, duplicate transactions or replay attacks
	Conflict = "409"
	// Request for resource is not available. Example, a chaincode has
	// been upgraded and the request uses an old version
	Gone = "410"
	// Payload of the request exceeds allowed size
	PayloadTooLarge = "413"
	// Example, marshal/unmarshalling protobuf error
	UnprocessableEntity = "422"
	// Protocol version is no longer supported
	UpgradeRequired = "426"
	// Internal server errors that are not classified below
	Internal = "500"
	// Requested chaincode function has not been implemented
	NotImplemented = "501"
	// Requested chaincode is not available
	Unavailable = "503"
	// File IO errors
	FileIO = "520"
	// Network IO errors
	NetworkIO = "521"
)
// BCCSP is fabic/BCCSP
const BCCSPconst = "CSP" //WAS:BCCSP

/*** fabric/common/errors/errors.go ***/
// MaxCallStackLength is the maximum length of the stored call stack
const MaxCallStackLength = 30
var (
	componentPattern = "[A-Za-z]{3}"
	reasonPattern    = "[0-9]{3}"
)
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
// Error creates a CallStackError using a specific component code and reason
// code (no callstack is generated)
func Error(componentcode string, reasoncode string, message string, args ...interface{}) CallStackError {
	return newError(componentcode, reasoncode, message, args...).GenerateStack(false)
}
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

/*** fabric/bccsp/sw/aes.go ***/
// GetRandomBytes returns len random looking bytes
func GetRandomBytesSW(len int) ([]byte, error) { //WAS:GetRandomBytes
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
func pkcs7Padding(src []byte) []byte {
	padding := aes.BlockSize - len(src)%aes.BlockSize
	padtext := bytes.Repeat([]byte{byte(padding)}, padding)
	return append(src, padtext...)
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
// AESCBCPKCS7Encrypt combines CBC encryption and PKCS7 padding
func AESCBCPKCS7Encrypt(key, src []byte) ([]byte, error) {
	// First pad
	tmp := pkcs7Padding(src)
	// Then encrypt
	return aesCBCEncrypt(key, tmp)
}
// AESCBCPKCS7Decrypt combines CBC decryption and PKCS7 unpadding
func AESCBCPKCS7Decrypt(key, src []byte) ([]byte, error) {
	// First decrypt
	pt, err := aesCBCDecrypt(key, src)
	if err == nil {
		return pkcs7UnPadding(pt)
	}
	return nil, err
}
type aescbcpkcs7Encryptor struct{}
func (*aescbcpkcs7Encryptor) Encrypt(k Key, plaintext []byte, opts EncrypterOpts) (ciphertext []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.EncrypterOpts
	switch opts.(type) {
	case *AESCBCPKCS7ModeOpts, AESCBCPKCS7ModeOpts: //SOURCE:bccsp.Key
		// AES in CBC mode with PKCS7 padding
		return AESCBCPKCS7Encrypt(k.(*aesPrivateKey).privKey, plaintext)
	default:
		return nil, fmt.Errorf("Mode not recognized [%s]", opts)
	}
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

/*** fabric/bccsp/sw/hash.go ***/
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

/*** fabric/bccsp/hashopts.go ***/
// SHA256Opts contains options relating to SHA-256.
type SHA256Opts struct {
}
// Algorithm returns the hash algorithm identifier (to be used).
func (opts *SHA256Opts) Algorithm() string {
	return SHA256
}
// SHA384Opts contains options relating to SHA-384.
type SHA384Opts struct {
}
// Algorithm returns the hash algorithm identifier (to be used).
func (opts *SHA384Opts) Algorithm() string {
	return SHA384
}
// SHA3_256Opts contains options relating to SHA3-256.
type SHA3_256Opts struct {
}
// Algorithm returns the hash algorithm identifier (to be used).
func (opts *SHA3_256Opts) Algorithm() string {
	return SHA3_256
}
// SHA3_384Opts contains options relating to SHA3-384.
type SHA3_384Opts struct {
}
// Algorithm returns the hash algorithm identifier (to be used).
func (opts *SHA3_384Opts) Algorithm() string {
	return SHA3_384
}
// GetHashOpt returns the HashOpts corresponding to the passed hash function
func GetHashOpt(hashFunction string) (HashOpts, error) {
	switch hashFunction {
	case SHA256:
		return &SHA256Opts{}, nil
	case SHA384:
		return &SHA384Opts{}, nil
	case SHA3_256:
		return &SHA3_256Opts{}, nil
	case SHA3_384:
		return &SHA3_384Opts{}, nil
	}
	return nil, fmt.Errorf("hash function not recognized [%s]", hashFunction)
}

/*** fabric/bccsp/sw/keygen.go ***/
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
	lowLevelKey, err := GetRandomBytesSW(int(kg.length)) //WAS:GetRandomBytes
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

/*** fabric/bccsp/sw/keyderiv.go ***/
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

/*** fabric/bccsp/sw/keyimport.go ***/
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

/*** fabric/bccsp/signer/signer.go ***/
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

/*** fabric/bccsp/sw/impl.go ***/
// New returns a new instance of the software-based BCCSP
// set at the passed security level, hash family and KeyStore.
func NewSW(securityLevel int, hashFamily string, keyStore KeyStore) (BCCSP, error) { //WAS:New //SOURCE:bccsp.KeyStore //SOURCE:bccsp.BCCSP
	// Init config
	conf := &config{}
	err := conf.setSecurityLevel(securityLevel, hashFamily)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed initializing configuration at [%v,%v]", securityLevel, hashFamily).WrapError(err) //SOURCE:bccsp.ErrorWithCallstack //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:bccsp.Internal
	}
	// Check KeyStore
	if keyStore == nil {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid bccsp.KeyStore instance. It must be different from nil.") //SOURCE:bccsp.ErrorWithCallstack //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:bccsp.BadRequest
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
func (csp *impl) KeyGen(opts KeyGenOpts) (k Key, err error) { //SOURCE:bccsp.KeyGenOpts //SOURCE:bccsp.Key
	// Validate arguments
	if opts == nil {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid Opts parameter. It must not be nil.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	keyGenerator, found := csp.keyGenerators[reflect.TypeOf(opts)]
	if !found {
		return nil, ErrorWithCallstack(BCCSPconst, NotFound, "Unsupported 'KeyGenOpts' provided [%v]", opts) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.NotFound
	}
	k, err = keyGenerator.KeyGen(opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed generating key with opts [%v]", opts).WrapError(err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
	}
	// If the key is not Ephemeral, store it.
	if !opts.Ephemeral() {
		// Store the key
		err = csp.ks.StoreKey(k)
		if err != nil {
			return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed storing key [%s]. [%s]", opts.Algorithm(), err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
		}
	}
	return k, nil
}
// KeyDeriv derives a key from k using opts.
// The opts argument should be appropriate for the primitive used.
func (csp *impl) KeyDeriv(k Key, opts KeyDerivOpts) (dk Key, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.KeyDerivOpts
	// Validate arguments
	if k == nil {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid Key. It must not be nil.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	if opts == nil {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid opts. It must not be nil.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	keyDeriver, found := csp.keyDerivers[reflect.TypeOf(k)]
	if !found {
		return nil, ErrorWithCallstack(BCCSPconst, NotFound, "Unsupported 'Key' provided [%v]", k) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.NotFound
	}
	k, err = keyDeriver.KeyDeriv(k, opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed deriving key with opts [%v]", opts).WrapError(err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
	}
	// If the key is not Ephemeral, store it.
	if !opts.Ephemeral() {
		// Store the key
		err = csp.ks.StoreKey(k)
		if err != nil {
			return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed storing key [%s]. [%s]", opts.Algorithm(), err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
		}
	}
	return k, nil
}
// KeyImport imports a key from its raw representation using opts.
// The opts argument should be appropriate for the primitive used.
func (csp *impl) KeyImport(raw interface{}, opts KeyImportOpts) (k Key, err error) { //SOURCE:bccsp.KeyImportOpts //SOURCE:bccsp.Key
	// Validate arguments
	if raw == nil {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid raw. It must not be nil.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	if opts == nil {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid opts. It must not be nil.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	keyImporter, found := csp.keyImporters[reflect.TypeOf(opts)]
	if !found {
		return nil, ErrorWithCallstack(BCCSPconst, NotFound, "Unsupported 'KeyImportOpts' provided [%v]", opts) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.NotFound
	}
	k, err = keyImporter.KeyImport(raw, opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed importing key with opts [%v]", opts).WrapError(err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
	}
	// If the key is not Ephemeral, store it.
	if !opts.Ephemeral() {
		// Store the key
		err = csp.ks.StoreKey(k)
		if err != nil {
			return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed storing imported key with opts [%v]", opts).WrapError(err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
		}
	}
	return
}
// GetKey returns the key this CSP associates to
// the Subject Key Identifier ski.
func (csp *impl) GetKey(ski []byte) (k Key, err error) { //SOURCE:bccsp.Key
	k, err = csp.ks.GetKey(ski)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed getting key for SKI [%v]", ski).WrapError(err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
	}
	return
}
// Hash hashes messages msg using options opts.
func (csp *impl) Hash(msg []byte, opts HashOpts) (digest []byte, err error) { //SOURCE:bccsp.HashOpts
	// Validate arguments
	if opts == nil {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid opts. It must not be nil.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	hasher, found := csp.hashers[reflect.TypeOf(opts)]
	if !found {
		return nil, ErrorWithCallstack(BCCSPconst, NotFound, "Unsupported 'HashOpt' provided [%v]", opts) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.NotFound
	}
	digest, err = hasher.Hash(msg, opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed hashing with opts [%v]", opts).WrapError(err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
	}
	return
}
// GetHash returns and instance of hash.Hash using options opts.
// If opts is nil then the default hash function is returned.
func (csp *impl) GetHash(opts HashOpts) (h hash.Hash, err error) { //SOURCE:bccsp.HashOpts
	// Validate arguments
	if opts == nil {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid opts. It must not be nil.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	hasher, found := csp.hashers[reflect.TypeOf(opts)]
	if !found {
		return nil, ErrorWithCallstack(BCCSPconst, NotFound, "Unsupported 'HashOpt' provided [%v]", opts) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.NotFound
	}
	h, err = hasher.GetHash(opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed getting hash function with opts [%v]", opts).WrapError(err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
	}
	return
}
// Sign signs digest using key k.
// The opts argument should be appropriate for the primitive used.
// Note that when a signature of a hash of a larger message is needed,
// the caller is responsible for hashing the larger message and passing
// the hash (as digest).
func (csp *impl) Sign(k Key, digest []byte, opts SignerOpts) (signature []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	// Validate arguments
	if k == nil {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid Key. It must not be nil.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	if len(digest) == 0 {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid digest. Cannot be empty.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	signer, found := csp.signers[reflect.TypeOf(k)]
	if !found {
		return nil, ErrorWithCallstack(BCCSPconst, NotFound, "Unsupported 'SignKey' provided [%v]", k) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.NotFound
	}
	signature, err = signer.Sign(k, digest, opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed signing with opts [%v]", opts).WrapError(err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
	}
	return
}
// Verify verifies signature against key k and digest
func (csp *impl) Verify(k Key, signature, digest []byte, opts SignerOpts) (valid bool, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.SignerOpts
	// Validate arguments
	if k == nil {
		return false, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid Key. It must not be nil.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	if len(signature) == 0 {
		return false, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid signature. Cannot be empty.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	if len(digest) == 0 {
		return false, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid digest. Cannot be empty.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	verifier, found := csp.verifiers[reflect.TypeOf(k)]
	if !found {
		return false, ErrorWithCallstack(BCCSPconst, NotFound, "Unsupported 'VerifyKey' provided [%v]", k) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.NotFound
	}
	valid, err = verifier.Verify(k, signature, digest, opts)
	if err != nil {
		return false, ErrorWithCallstack(BCCSPconst, Internal, "Failed verifing with opts [%v]", opts).WrapError(err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
	}
	return
}
// Encrypt encrypts plaintext using key k.
// The opts argument should be appropriate for the primitive used.
func (csp *impl) Encrypt(k Key, plaintext []byte, opts EncrypterOpts) (ciphertext []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.EncrypterOpts
	// Validate arguments
	if k == nil {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid Key. It must not be nil.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	encryptor, found := csp.encryptors[reflect.TypeOf(k)]
	if !found {
		return nil, ErrorWithCallstack(BCCSPconst, NotFound, "Unsupported 'EncryptKey' provided [%v]", k) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.NotFound
	}
	return encryptor.Encrypt(k, plaintext, opts)
}
// Decrypt decrypts ciphertext using key k.
// The opts argument should be appropriate for the primitive used.
func (csp *impl) Decrypt(k Key, ciphertext []byte, opts DecrypterOpts) (plaintext []byte, err error) { //SOURCE:bccsp.Key //SOURCE:bccsp.DecrypterOpts
	// Validate arguments
	if k == nil {
		return nil, ErrorWithCallstack(BCCSPconst, BadRequest, "Invalid Key. It must not be nil.") //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.BadRequest
	}
	decryptor, found := csp.decryptors[reflect.TypeOf(k)]
	if !found {
		return nil, ErrorWithCallstack(BCCSPconst, NotFound, "Unsupported 'DecryptKey' provided [%v]", k) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.NotFound
	}
	plaintext, err = decryptor.Decrypt(k, ciphertext, opts)
	if err != nil {
		return nil, ErrorWithCallstack(BCCSPconst, Internal, "Failed decrypting with opts [%v]", opts).WrapError(err) //WAS:BCCSP //SOURCE:errors.BCCSP //SOURCE:errors.Internal
	}
	return
}

/*** fabric/bccsp/sw/fileks.go ***/
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

/*** fabric/bccsp/factory/swfactory.go ***/
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
	return NewSW(swOpts.SecLevel, swOpts.HashFamily, ks) //WAS:New //SOURCE:sw.New
}
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
// Pluggable Keystores, could add JKS, P12, etc..
type FileKeystoreOpts struct {
	KeyStorePath string `mapstructure:"keystore" yaml:"KeyStore"`
}
type DummyKeystoreOpts struct{}

/*** fabric/bccsp/factory/factory.go ***/
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

/*** fabric/protos/msp/msp_principal.pb.go ***/
type MSPPrincipal_Classification int32
const (
	MSPPrincipal_ROLE MSPPrincipal_Classification = 0
	// one of a member of MSP network, and the one of an
	// administrator of an MSP network
	MSPPrincipal_ORGANIZATION_UNIT MSPPrincipal_Classification = 1
	// groupping of entities, per MSP affiliation
	// E.g., this can well be represented by an MSP's
	// Organization unit
	MSPPrincipal_IDENTITY MSPPrincipal_Classification = 2
)
type MSPRole_MSPRoleType int32
const (
	MSPRole_MEMBER MSPRole_MSPRoleType = 0
	MSPRole_ADMIN  MSPRole_MSPRoleType = 1
)
// MSPPrincipal aims to represent an MSP-centric set of identities.
// In particular, this structure allows for definition of
//  - a group of identities that are member of the same MSP
//  - a group of identities that are member of the same organization unit
//    in the same MSP
//  - a group of identities that are administering a specific MSP
//  - a specific identity
// Expressing these groups is done given two fields of the fields below
//  - Classification, that defines the type of classification of identities
//    in an MSP this principal would be defined on; Classification can take
//    three values:
//     (i)  ByMSPRole: that represents a classification of identities within
//          MSP based on one of the two pre-defined MSP rules, "member" and "admin"
//     (ii) ByOrganizationUnit: that represents a classification of identities
//          within MSP based on the organization unit an identity belongs to
//     (iii)ByIdentity that denotes that MSPPrincipal is mapped to a single
//          identity/certificate; this would mean that the Principal bytes
//          message
type MSPPrincipal struct {
	// Classification describes the way that one should process
	// Principal. An Classification value of "ByOrganizationUnit" reflects
	// that "Principal" contains the name of an organization this MSP
	// handles. A Classification value "ByIdentity" means that
	// "Principal" contains a specific identity. Default value
	// denotes that Principal contains one of the groups by
	// default supported by all MSPs ("admin" or "member").
	PrincipalClassification MSPPrincipal_Classification `protobuf:"varint,1,opt,name=principal_classification,json=principalClassification,enum=common.MSPPrincipal_Classification" json:"principal_classification,omitempty"`
	// Principal completes the policy principal definition. For the default
	// principal types, Principal can be either "Admin" or "Member".
	// For the ByOrganizationUnit/ByIdentity values of Classification,
	// PolicyPrincipal acquires its value from an organization unit or
	// identity, respectively.
	Principal []byte `protobuf:"bytes,2,opt,name=principal,proto3" json:"principal,omitempty"`
}
func (m *MSPPrincipal) Reset()                    { *m = MSPPrincipal{} }
func (m *MSPPrincipal) String() string            { return proto.CompactTextString(m) }
func (*MSPPrincipal) ProtoMessage()               {}
func (*MSPPrincipal) Descriptor() ([]byte, []int) { return fileDescriptor2, []int{0} }
func (m *MSPPrincipal) GetPrincipalClassification() MSPPrincipal_Classification {
	if m != nil {
		return m.PrincipalClassification
	}
	return MSPPrincipal_ROLE
}
func (m *MSPPrincipal) GetPrincipal() []byte {
	if m != nil {
		return m.Principal
	}
	return nil
}
// OrganizationUnit governs the organization of the Principal
// field of a policy principal when a specific organization unity members
// are to be defined within a policy principal.
type OrganizationUnit struct {
	// MSPIdentifier represents the identifier of the MSP this organization unit
	// refers to
	MspIdentifier string `protobuf:"bytes,1,opt,name=msp_identifier,json=mspIdentifier" json:"msp_identifier,omitempty"`
	// OrganizationUnitIdentifier defines the organizational unit under the
	// MSP identified with MSPIdentifier
	OrganizationalUnitIdentifier string `protobuf:"bytes,2,opt,name=organizational_unit_identifier,json=organizationalUnitIdentifier" json:"organizational_unit_identifier,omitempty"`
	// CertifiersIdentifier is the hash of certificates chain of trust
	// related to this organizational unit
	CertifiersIdentifier []byte `protobuf:"bytes,3,opt,name=certifiers_identifier,json=certifiersIdentifier,proto3" json:"certifiers_identifier,omitempty"`
}
func (m *OrganizationUnit) Reset()                    { *m = OrganizationUnit{} }
func (m *OrganizationUnit) String() string            { return proto.CompactTextString(m) }
func (*OrganizationUnit) ProtoMessage()               {}
func (*OrganizationUnit) Descriptor() ([]byte, []int) { return fileDescriptor2, []int{1} }
func (m *OrganizationUnit) GetMspIdentifier() string {
	if m != nil {
		return m.MspIdentifier
	}
	return ""
}
func (m *OrganizationUnit) GetOrganizationalUnitIdentifier() string {
	if m != nil {
		return m.OrganizationalUnitIdentifier
	}
	return ""
}
func (m *OrganizationUnit) GetCertifiersIdentifier() []byte {
	if m != nil {
		return m.CertifiersIdentifier
	}
	return nil
}
// MSPRole governs the organization of the Principal
// field of an MSPPrincipal when it aims to define one of the
// two dedicated roles within an MSP: Admin and Members.
type MSPRole struct {
	// MSPIdentifier represents the identifier of the MSP this principal
	// refers to
	MspIdentifier string `protobuf:"bytes,1,opt,name=msp_identifier,json=mspIdentifier" json:"msp_identifier,omitempty"`
	// MSPRoleType defines which of the available, pre-defined MSP-roles
	// an identiy should posess inside the MSP with identifier MSPidentifier
	Role MSPRole_MSPRoleType `protobuf:"varint,2,opt,name=role,enum=common.MSPRole_MSPRoleType" json:"role,omitempty"`
}
func (m *MSPRole) Reset()                    { *m = MSPRole{} }
func (m *MSPRole) String() string            { return proto.CompactTextString(m) }
func (*MSPRole) ProtoMessage()               {}
func (*MSPRole) Descriptor() ([]byte, []int) { return fileDescriptor2, []int{2} }
func (m *MSPRole) GetMspIdentifier() string {
	if m != nil {
		return m.MspIdentifier
	}
	return ""
}
func (m *MSPRole) GetRole() MSPRole_MSPRoleType {
	if m != nil {
		return m.Role
	}
	return MSPRole_MEMBER
}

/*** fabric/protos/msp/identities.pb.go ***/
// This struct represents an Identity
// (with its MSP identifier) to be used
// to serialize it and deserialize it
type SerializedIdentity struct {
	// The identifier of the associated membership service provider
	Mspid string `protobuf:"bytes,1,opt,name=mspid" json:"mspid,omitempty"`
	// the Identity, serialized according to the rules of its MPS
	IdBytes []byte `protobuf:"bytes,2,opt,name=id_bytes,json=idBytes,proto3" json:"id_bytes,omitempty"`
}
func (m *SerializedIdentity) Reset()                    { *m = SerializedIdentity{} }
func (m *SerializedIdentity) String() string            { return proto.CompactTextString(m) }
func (*SerializedIdentity) ProtoMessage()               {}
func (*SerializedIdentity) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{0} }
func (m *SerializedIdentity) GetMspid() string {
	if m != nil {
		return m.Mspid
	}
	return ""
}
func (m *SerializedIdentity) GetIdBytes() []byte {
	if m != nil {
		return m.IdBytes
	}
	return nil
}

/*** fabric/msp/msp.go ***/
// IdentityDeserializer is implemented by both MSPManger and MSP
type IdentityDeserializer interface {
	// DeserializeIdentity deserializes an identity.
	// Deserialization will fail if the identity is associated to
	// an msp that is different from this one that is performing
	// the deserialization.
	DeserializeIdentity(serializedIdentity []byte) (Identity, error)
}
// Membership service provider APIs for Hyperledger Fabric:
//
// By "membership service provider" we refer to an abstract component of the
// system that would provide (anonymous) credentials to clients, and peers for
// them to participate in Hyperledger/fabric network. Clients use these
// credentials to authenticate their transactions, and peers use these credentials
// to authenticate transaction processing results (endorsements). While
// strongly connected to the transaction processing components of the systems,
// this interface aims to have membership services components defined, in such
// a way such that alternate implementations of this can be smoothly plugged in
// without modifying the core of transaction processing components of the system.
//
// This file includes Membership service provider interface that covers the
// needs of a peer membership service provider interface.

// MSPManager is an interface defining a manager of one or more MSPs. This
// essentially acts as a mediator to MSP calls and routes MSP related calls
// to the appropriate MSP.
// This object is immutable, it is initialized once and never changed.
type MSPManager interface {
	// IdentityDeserializer interface needs to be implemented by MSPManager
	IdentityDeserializer
	// Setup the MSP manager instance according to configuration information
	Setup(msps []MSP) error
	// GetMSPs Provides a list of Membership Service providers
	GetMSPs() (map[string]MSP, error)
}
// MSP is the minimal Membership Service Provider Interface to be implemented
// to accommodate peer functionality
type MSP interface {
	// IdentityDeserializer interface needs to be implemented by MSP
	IdentityDeserializer
	// Setup the MSP instance according to configuration information
	Setup(config *MSPConfig) error //SOURCE:msp.MSPConfig
	// GetType returns the provider type
	GetType() ProviderType
	// GetIdentifier returns the provider identifier
	GetIdentifier() (string, error)
	// GetSigningIdentity returns a signing identity corresponding to the provided identifier
	GetSigningIdentity(identifier *IdentityIdentifier) (SigningIdentity, error)
	// GetDefaultSigningIdentity returns the default signing identity
	GetDefaultSigningIdentity() (SigningIdentity, error)
	// GetTLSRootCerts returns the TLS root certificates for this MSP
	GetTLSRootCerts() [][]byte
	// GetTLSIntermediateCerts returns the TLS intermediate root certificates for this MSP
	GetTLSIntermediateCerts() [][]byte
	// Validate checks whether the supplied identity is valid
	Validate(id Identity) error
	// SatisfiesPrincipal checks whether the identity matches
	// the description supplied in MSPPrincipal. The check may
	// involve a byte-by-byte comparison (if the principal is
	// a serialized identity) or may require MSP validation
	SatisfiesPrincipal(id Identity, principal *MSPPrincipal) error //SOURCE:msp.MSPPrincipal
}
// OUIdentifier represents an organizational unit and
// its related chain of trust identifier.
type OUIdentifier struct {
	// CertifiersIdentifier is the hash of certificates chain of trust
	// related to this organizational unit
	CertifiersIdentifier []byte
	// OrganizationUnitIdentifier defines the organizational unit under the
	// MSP identified with MSPIdentifier
	OrganizationalUnitIdentifier string
}
// Identity interface defining operations associated to a "certificate".
// That is, the public part of the identity could be thought to be a certificate,
// and offers solely signature verification capabilities. This is to be used
// at the peer side when verifying certificates that transactions are signed
// with, and verifying signatures that correspond to these certificates.///
type Identity interface {
	// GetIdentifier returns the identifier of that identity
	GetIdentifier() *IdentityIdentifier
	// GetMSPIdentifier returns the MSP Id for this instance
	GetMSPIdentifier() string
	// Validate uses the rules that govern this identity to validate it.
	// E.g., if it is a fabric TCert implemented as identity, validate
	// will check the TCert signature against the assumed root certificate
	// authority.
	Validate() error
	// GetOrganizationalUnits returns zero or more organization units or
	// divisions this identity is related to as long as this is public
	// information. Certain MSP implementations may use attributes
	// that are publicly associated to this identity, or the identifier of
	// the root certificate authority that has provided signatures on this
	// certificate.
	// Examples:
	//  - if the identity is an x.509 certificate, this function returns one
	//    or more string which is encoded in the Subject's Distinguished Name
	//    of the type OU
	// TODO: For X.509 based identities, check if we need a dedicated type
	//       for OU where the Certificate OU is properly namespaced by the
	//       signer's identity
	GetOrganizationalUnits() []*OUIdentifier
	// Verify a signature over some message using this identity as reference
	Verify(msg []byte, sig []byte) error
	// Serialize converts an identity to bytes
	Serialize() ([]byte, error)
	// SatisfiesPrincipal checks whether this instance matches
	// the description supplied in MSPPrincipal. The check may
	// involve a byte-by-byte comparison (if the principal is
	// a serialized identity) or may require MSP validation
	SatisfiesPrincipal(principal *MSPPrincipal) error //SOURCE:msp.MSPPrincipal
}
// SigningIdentity is an extension of Identity to cover signing capabilities.
// E.g., signing identity should be requested in the case of a client who wishes
// to sign transactions, or fabric endorser who wishes to sign proposal
// processing outcomes.
type SigningIdentity interface {
	// Extends Identity
	Identity
	// Sign the message
	Sign(msg []byte) ([]byte, error)
	// GetPublicVersion returns the public parts of this identity
	GetPublicVersion() Identity
}
// IdentityIdentifier is a holder for the identifier of a specific
// identity, naturally namespaced, by its provider identifier.
type IdentityIdentifier struct {
	// The identifier of the associated membership service provider
	Mspid string
	// The identifier for an identity within a provider
	Id string
}
// ProviderType indicates the type of an identity provider
type ProviderType int
// The ProviderType of a member relative to the member API
const FABRIC ProviderType = iota // MSP is of FABRIC type

/*** fabric/msp/mspmgrimpl.go ***/
var mspLogger = MustGetLogger("msp") //SOURCE:flogging.MustGetLogger

/*** fabric/msp/cert.go ***/
type validity struct {
	NotBefore, NotAfter time.Time
}
type publicKeyInfo struct {
	Raw       asn1.RawContent
	Algorithm pkix.AlgorithmIdentifier
	PublicKey asn1.BitString
}
type certificate struct {
	Raw                asn1.RawContent
	TBSCertificate     tbsCertificate
	SignatureAlgorithm pkix.AlgorithmIdentifier
	SignatureValue     asn1.BitString
}
type tbsCertificate struct {
	Raw                asn1.RawContent
	Version            int `asn1:"optional,explicit,default:0,tag:0"`
	SerialNumber       *big.Int
	SignatureAlgorithm pkix.AlgorithmIdentifier
	Issuer             asn1.RawValue
	Validity           validity
	Subject            asn1.RawValue
	PublicKey          publicKeyInfo
	UniqueId           asn1.BitString   `asn1:"optional,tag:1"`
	SubjectUniqueId    asn1.BitString   `asn1:"optional,tag:2"`
	Extensions         []pkix.Extension `asn1:"optional,explicit,tag:3"`
}
func isECDSASignedCert(cert *x509.Certificate) bool {
	return cert.SignatureAlgorithm == x509.ECDSAWithSHA1 ||
		cert.SignatureAlgorithm == x509.ECDSAWithSHA256 ||
		cert.SignatureAlgorithm == x509.ECDSAWithSHA384 ||
		cert.SignatureAlgorithm == x509.ECDSAWithSHA512
}
// sanitizeECDSASignedCert checks that the signatures signing a cert
// is in low-S. This is checked against the public key of parentCert.
// If the signature is not in low-S, then a new certificate is generated
// that is equals to cert but the signature that is in low-S.
func sanitizeECDSASignedCert(cert *x509.Certificate, parentCert *x509.Certificate) (*x509.Certificate, error) {
	if cert == nil {
		return nil, errors.New("Certificate must be different from nil.")
	}
	if parentCert == nil {
		return nil, errors.New("Parent certificate must be different from nil.")
	}
	expectedSig, err := SignatureToLowS(parentCert.PublicKey.(*ecdsa.PublicKey), cert.Signature) //SOURCE:sw.SignatureToLowS
	if err != nil {
		return nil, err
	}
	// if sig == cert.Signature, nothing needs to be done
	if bytes.Equal(cert.Signature, expectedSig) {
		return cert, nil
	}
	// otherwise create a new certificate with the new signature
	// 1. Unmarshal cert.Raw to get an instance of certificate,
	//    the lower level interface that represent an x509 certificate
	//    encoding
	var newCert certificate
	newCert, err = certFromX509Cert(cert)
	if err != nil {
		return nil, err
	}
	// 2. Change the signature
	newCert.SignatureValue = asn1.BitString{Bytes: expectedSig, BitLength: len(expectedSig) * 8}
	// 3. marshal again newCert. Raw must be nil
	newCert.Raw = nil
	newRaw, err := asn1.Marshal(newCert)
	if err != nil {
		return nil, err
	}
	// 4. parse newRaw to get an x509 certificate
	return x509.ParseCertificate(newRaw)
}
func certFromX509Cert(cert *x509.Certificate) (certificate, error) {
	var newCert certificate
	_, err := asn1.Unmarshal(cert.Raw, &newCert)
	if err != nil {
		return certificate{}, err
	}
	return newCert, nil
}
// String returns a PEM representation of a certificate
func (c certificate) String() string {
	b, err := asn1.Marshal(c)
	if err != nil {
		return fmt.Sprintf("Failed marshaling cert: %v", err)
	}
	block := &pem.Block{
		Bytes: b,
		Type:  "CERTIFICATE",
	}
	b = pem.EncodeToMemory(block)
	return string(b)
}
// certToPEM converts the given x509.Certificate to a PEM
// encoded string
func certToPEM(certificate *x509.Certificate) string {
	cert, err := certFromX509Cert(certificate)
	if err != nil {
		mspIdentityLogger.Warning("Failed converting certificate to asn1", err)
		return ""
	}
	return cert.String()
}

/*** fabric/msp/identities.go ***/
var mspIdentityLogger = MustGetLogger("msp/identity") //SOURCE:flogging.MustGetLogger
type identity struct {
	// id contains the identifier (MSPID and identity identifier) for this instance
	id *IdentityIdentifier
	// cert contains the x.509 certificate that signs the public key of this instance
	cert *x509.Certificate
	// this is the public key of this instance
	pk Key //SOURCE:bccsp.Key
	// reference to the MSP that "owns" this identity
	msp *bccspmsp
}
func newIdentity(id *IdentityIdentifier, cert *x509.Certificate, pk Key, msp *bccspmsp) (Identity, error) { //SOURCE:bccsp.Key
	mspIdentityLogger.Debugf("Creating identity instance for ID %s", certToPEM(cert))
	// Sanitize first the certificate
	cert, err := msp.sanitizeCert(cert)
	if err != nil {
		return nil, err
	}
	return &identity{id: id, cert: cert, pk: pk, msp: msp}, nil
}
// SatisfiesPrincipal returns null if this instance matches the supplied principal or an error otherwise
func (id *identity) SatisfiesPrincipal(principal *MSPPrincipal) error { //SOURCE:msp.MSPPrincipal
	return id.msp.SatisfiesPrincipal(id, principal)
}
// GetIdentifier returns the identifier (MSPID/IDID) for this instance
func (id *identity) GetIdentifier() *IdentityIdentifier {
	return id.id
}
// GetMSPIdentifier returns the MSP identifier for this instance
func (id *identity) GetMSPIdentifier() string {
	return id.id.Mspid
}
// IsValid returns nil if this instance is a valid identity or an error otherwise
func (id *identity) Validate() error {
	return id.msp.Validate(id)
}
// GetOrganizationalUnits returns the OU for this instance
func (id *identity) GetOrganizationalUnits() []*OUIdentifier {
	if id.cert == nil {
		return nil
	}
	cid, err := id.msp.getCertificationChainIdentifier(id)
	if err != nil {
		mspIdentityLogger.Errorf("Failed getting certification chain identifier for [%v]: [%s]", id, err)
		return nil
	}
	res := []*OUIdentifier{}
	for _, unit := range id.cert.Subject.OrganizationalUnit {
		res = append(res, &OUIdentifier{
			OrganizationalUnitIdentifier: unit,
			CertifiersIdentifier:         cid,
		})
	}
	return res
}
// Verify checks against a signature and a message
// to determine whether this identity produced the
// signature; it returns nil if so or an error otherwise
func (id *identity) Verify(msg []byte, sig []byte) error {
	// mspIdentityLogger.Infof("Verifying signature")
	// Compute Hash
	hashOpt, err := id.getHashOpt(id.msp.cryptoConfig.SignatureHashFamily)
	if err != nil {
		return fmt.Errorf("Failed getting hash function options [%s]", err)
	}
	digest, err := id.msp.bccsp.Hash(msg, hashOpt)
	if err != nil {
		return fmt.Errorf("Failed computing digest [%s]", err)
	}
	if mspIdentityLogger.IsEnabledFor(logging.DEBUG) {
		mspIdentityLogger.Debugf("Verify: digest = %s", hex.Dump(digest))
		mspIdentityLogger.Debugf("Verify: sig = %s", hex.Dump(sig))
	}
	valid, err := id.msp.bccsp.Verify(id.pk, sig, digest, nil)
	if err != nil {
		return fmt.Errorf("Could not determine the validity of the signature, err %s", err)
	} else if !valid {
		return errors.New("The signature is invalid")
	}
	return nil
}
// Serialize returns a byte array representation of this identity
func (id *identity) Serialize() ([]byte, error) {
	// mspIdentityLogger.Infof("Serializing identity %s", id.id)
	pb := &pem.Block{Bytes: id.cert.Raw}
	pemBytes := pem.EncodeToMemory(pb)
	if pemBytes == nil {
		return nil, fmt.Errorf("Encoding of identitiy failed")
	}
	// We serialize identities by prepending the MSPID and appending the ASN.1 DER content of the cert
	sId := &SerializedIdentity{Mspid: id.id.Mspid, IdBytes: pemBytes} //SOURCE:msp.SerializedIdentity
	idBytes, err := proto.Marshal(sId)
	if err != nil {
		return nil, fmt.Errorf("Could not marshal a SerializedIdentity structure for identity %s, err %s", id.id, err)
	}
	return idBytes, nil
}
func (id *identity) getHashOpt(hashFamily string) (HashOpts, error) { //SOURCE:bccsp.HashOpts
	switch hashFamily {
	case SHA2: //SOURCE:bccsp.SHA2
		return GetHashOpt(SHA256) //SOURCE:bccsp.GetHashOpt //SOURCE:bccsp.SHA256
	case SHA3: //SOURCE:bccsp.SHA3
		return GetHashOpt(SHA3_256) //SOURCE:bccsp.GetHashOpt //SOURCE:bccsp.SHA3_256
	}
	return nil, fmt.Errorf("hash famility not recognized [%s]", hashFamily)
}
type signingidentity struct {
	// we embed everything from a base identity
	identity
	// signer corresponds to the object that can produce signatures from this identity
	signer crypto.Signer
}
func newSigningIdentity(id *IdentityIdentifier, cert *x509.Certificate, pk Key, signer crypto.Signer, msp *bccspmsp) (SigningIdentity, error) { //SOURCE:bccsp.Key
	//mspIdentityLogger.Infof("Creating signing identity instance for ID %s", id)
	mspId, err := newIdentity(id, cert, pk, msp)
	if err != nil {
		return nil, err
	}
	return &signingidentity{identity: *mspId.(*identity), signer: signer}, nil
}
// Sign produces a signature over msg, signed by this instance
func (id *signingidentity) Sign(msg []byte) ([]byte, error) {
	//mspIdentityLogger.Infof("Signing message")
	// Compute Hash
	hashOpt, err := id.getHashOpt(id.msp.cryptoConfig.SignatureHashFamily)
	if err != nil {
		return nil, fmt.Errorf("Failed getting hash function options [%s]", err)
	}
	digest, err := id.msp.bccsp.Hash(msg, hashOpt)
	if err != nil {
		return nil, fmt.Errorf("Failed computing digest [%s]", err)
	}
	if len(msg) < 32 {
		mspIdentityLogger.Debugf("Sign: plaintext: %X \n", msg)
	} else {
		mspIdentityLogger.Debugf("Sign: plaintext: %X...%X \n", msg[0:16], msg[len(msg)-16:])
	}
	mspIdentityLogger.Debugf("Sign: digest: %X \n", digest)
	// Sign
	return id.signer.Sign(rand.Reader, digest, nil)
}
func (id *signingidentity) GetPublicVersion() Identity {
	return &id.identity
}

/*** fabric/msp/mspimpl.go ***/
// This is an instantiation of an MSP that
// uses BCCSP for its cryptographic primitives.
type bccspmsp struct {
	// list of CA certs we trust
	rootCerts []Identity
	// list of intermediate certs we trust
	intermediateCerts []Identity
	// list of CA TLS certs we trust
	tlsRootCerts [][]byte
	// list of intermediate TLS certs we trust
	tlsIntermediateCerts [][]byte
	// certificationTreeInternalNodesMap whose keys correspond to the raw material
	// (DER representation) of a certificate casted to a string, and whose values
	// are boolean. True means that the certificate is an internal node of the certification tree.
	// False means that the certificate corresponds to a leaf of the certification tree.
	certificationTreeInternalNodesMap map[string]bool
	// list of signing identities
	signer SigningIdentity
	// list of admin identities
	admins []Identity
	// the crypto provider
	bccsp BCCSP //SOURCE:bccsp.BCCSP
	// the provider identifier for this MSP
	name string
	// verification options for MSP members
	opts *x509.VerifyOptions
	// list of certificate revocation lists
	CRL []*pkix.CertificateList
	// list of OUs
	ouIdentifiers map[string][][]byte
	// cryptoConfig contains
	cryptoConfig *FabricCryptoConfig //SOURCE:m.FabricCryptoConfig
}
// NewBccspMsp returns an MSP instance backed up by a BCCSP
// crypto provider. It handles x.509 certificates and can
// generate identities and signing identities backed by
// certificates and keypairs
func NewBccspMsp() (MSP, error) {
	mspLogger.Debugf("Creating BCCSP-based MSP instance")
	bccsp := GetDefault() //SOURCE:factory.GetDefault
	theMsp := &bccspmsp{}
	theMsp.bccsp = bccsp
	return theMsp, nil
}
func (msp *bccspmsp) getCertFromPem(idBytes []byte) (*x509.Certificate, error) {
	if idBytes == nil {
		return nil, fmt.Errorf("getIdentityFromConf error: nil idBytes")
	}
	// Decode the pem bytes
	pemCert, _ := pem.Decode(idBytes)
	if pemCert == nil {
		return nil, fmt.Errorf("getIdentityFromBytes error: could not decode pem bytes [%v]", idBytes)
	}
	// get a cert
	var cert *x509.Certificate
	cert, err := x509.ParseCertificate(pemCert.Bytes)
	if err != nil {
		return nil, fmt.Errorf("getIdentityFromBytes error: failed to parse x509 cert, err %s", err)
	}
	return cert, nil
}
func (msp *bccspmsp) getIdentityFromConf(idBytes []byte) (Identity, Key, error) { //SOURCE:bccsp.Key
	// get a cert
	cert, err := msp.getCertFromPem(idBytes)
	if err != nil {
		return nil, nil, err
	}
	// get the public key in the right format
	certPubK, err := msp.bccsp.KeyImport(cert, &X509PublicKeyImportOpts{Temporary: true}) //SOURCE:bccsp.X509PublicKeyImportOpts
	// Use the hash of the identity's certificate as id in the IdentityIdentifier
	hashOpt, err := GetHashOpt(msp.cryptoConfig.IdentityIdentifierHashFunction) //SOURCE:bccsp.GetHashOpt
	if err != nil {
		return nil, nil, fmt.Errorf("getIdentityFromConf failed getting hash function options [%s]", err)
	}
	digest, err := msp.bccsp.Hash(cert.Raw, hashOpt)
	if err != nil {
		return nil, nil, fmt.Errorf("getIdentityFromConf failed hashing raw certificate to compute the id of the IdentityIdentifier [%s]", err)
	}
	id := &IdentityIdentifier{
		Mspid: msp.name,
		Id:    hex.EncodeToString(digest)}
	mspId, err := newIdentity(id, cert, certPubK, msp)
	if err != nil {
		return nil, nil, err
	}
	return mspId, certPubK, nil
}
func (msp *bccspmsp) getSigningIdentityFromConf(sidInfo *SigningIdentityInfo) (SigningIdentity, error) { //SOURCE:m.SigningIdentityInfo
	if sidInfo == nil {
		return nil, fmt.Errorf("getIdentityFromBytes error: nil sidInfo")
	}
	// Extract the public part of the identity
	idPub, pubKey, err := msp.getIdentityFromConf(sidInfo.PublicSigner)
	if err != nil {
		return nil, err
	}
	// Find the matching private key in the BCCSP keystore
	privKey, err := msp.bccsp.GetKey(pubKey.SKI())
	// Less Secure: Attempt to import Private Key from KeyInfo, if BCCSP was not able to find the key
	if err != nil {
		mspLogger.Debugf("Could not find SKI [%s], trying KeyMaterial field: %s\n", hex.EncodeToString(pubKey.SKI()), err)
		if sidInfo.PrivateSigner == nil || sidInfo.PrivateSigner.KeyMaterial == nil {
			return nil, fmt.Errorf("KeyMaterial not found in SigningIdentityInfo")
		}
		pemKey, _ := pem.Decode(sidInfo.PrivateSigner.KeyMaterial)
		privKey, err = msp.bccsp.KeyImport(pemKey.Bytes, &ECDSAPrivateKeyImportOpts{Temporary: true}) //SOURCE:bccsp.ECDSAPrivateKeyImportOpts
		if err != nil {
			return nil, fmt.Errorf("getIdentityFromBytes error: Failed to import EC private key, err %s", err)
		}
	}
	// get the peer signer
	peerSigner, err := NewSigner(msp.bccsp, privKey)
	if err != nil {
		return nil, fmt.Errorf("getIdentityFromBytes error: Failed initializing bccspCryptoSigner, err %s", err)
	}
	// Use the hash of the identity's certificate as id in the IdentityIdentifier
	hashOpt, err := GetHashOpt(msp.cryptoConfig.IdentityIdentifierHashFunction) //SOURCE:bccsp.GetHashOpt
	if err != nil {
		return nil, fmt.Errorf("getIdentityFromBytes failed getting hash function options [%s]", err)
	}
	digest, err := msp.bccsp.Hash(idPub.(*identity).cert.Raw, hashOpt)
	if err != nil {
		return nil, fmt.Errorf("Failed hashing raw certificate to compute the id of the IdentityIdentifier [%s]", err)
	}
	id := &IdentityIdentifier{
		Mspid: msp.name,
		Id:    hex.EncodeToString(digest)}
	return newSigningIdentity(id, idPub.(*identity).cert, idPub.(*identity).pk, peerSigner, msp)
}
type authorityKeyIdentifier struct {
	KeyIdentifier             []byte  `asn1:"optional,tag:0"`
	AuthorityCertIssuer       []byte  `asn1:"optional,tag:1"`
	AuthorityCertSerialNumber big.Int `asn1:"optional,tag:2"`
}
// getAuthorityKeyIdentifierFromCrl returns the Authority Key Identifier
// for the supplied CRL. The authority key identifier can be used to identify
// the public key corresponding to the private key which was used to sign the CRL.
func getAuthorityKeyIdentifierFromCrl(crl *pkix.CertificateList) ([]byte, error) {
	aki := authorityKeyIdentifier{}
	for _, ext := range crl.TBSCertList.Extensions {
		// Authority Key Identifier is identified by the following ASN.1 tag
		// authorityKeyIdentifier (2 5 29 35) (see https://tools.ietf.org/html/rfc3280.html)
		if reflect.DeepEqual(ext.Id, asn1.ObjectIdentifier{2, 5, 29, 35}) {
			_, err := asn1.Unmarshal(ext.Value, &aki)
			if err != nil {
				return nil, fmt.Errorf("Failed to unmarshal AKI, error %s", err)
			}
			return aki.KeyIdentifier, nil
		}
	}
	return nil, errors.New("authorityKeyIdentifier not found in certificate")
}
// getSubjectKeyIdentifierFromCert returns the Subject Key Identifier for the supplied certificate
// Subject Key Identifier is an identifier of the public key of this certificate
func getSubjectKeyIdentifierFromCert(cert *x509.Certificate) ([]byte, error) {
	var SKI []byte
	for _, ext := range cert.Extensions {
		// Subject Key Identifier is identified by the following ASN.1 tag
		// subjectKeyIdentifier (2 5 29 14) (see https://tools.ietf.org/html/rfc3280.html)
		if reflect.DeepEqual(ext.Id, asn1.ObjectIdentifier{2, 5, 29, 14}) {
			_, err := asn1.Unmarshal(ext.Value, &SKI)
			if err != nil {
				return nil, fmt.Errorf("Failed to unmarshal Subject Key Identifier, err %s", err)
			}
			return SKI, nil
		}
	}
	return nil, errors.New("subjectKeyIdentifier not found in certificate")
}
// isCACert does a few checks on the certificate,
// assuming it's a CA; it returns true if all looks good
// and false otherwise
func isCACert(cert *x509.Certificate) bool {
	_, err := getSubjectKeyIdentifierFromCert(cert)
	if err != nil {
		return false
	}
	if !cert.IsCA {
		return false
	}
	return true
}
// Setup sets up the internal data structures
// for this MSP, given an MSPConfig ref; it
// returns nil in case of success or an error otherwise
func (msp *bccspmsp) Setup(conf1 *MSPConfig) error { //SOURCE:m.MSPConfig
	if conf1 == nil {
		return fmt.Errorf("Setup error: nil conf reference")
	}
	// given that it's an msp of type fabric, extract the MSPConfig instance
	conf := &FabricMSPConfig{} //SOURCE:m.FabricMSPConfig
	err := proto.Unmarshal(conf1.Config, conf)
	if err != nil {
		return fmt.Errorf("Failed unmarshalling fabric msp config, err %s", err)
	}
	// set the name for this msp
	msp.name = conf.Name
	mspLogger.Debugf("Setting up MSP instance %s", msp.name)
	// setup crypto config
	if err := msp.setupCrypto(conf); err != nil {
		return err
	}
	// Setup CAs
	if err := msp.setupCAs(conf); err != nil {
		return err
	}
	// Setup Admins
	if err := msp.setupAdmins(conf); err != nil {
		return err
	}
	// Setup CRLs
	if err := msp.setupCRLs(conf); err != nil {
		return err
	}
	// Finalize setup of the CAs
	if err := msp.finalizeSetupCAs(conf); err != nil {
		return err
	}
	// setup the signer (if present)
	if err := msp.setupSigningIdentity(conf); err != nil {
		return err
	}
	// setup the OUs
	if err := msp.setupOUs(conf); err != nil {
		return err
	}
	// setup TLS CAs
	if err := msp.setupTLSCAs(conf); err != nil {
		return err
	}
	// make sure that admins are valid members as well
	// this way, when we validate an admin MSP principal
	// we can simply check for exact match of certs
	for i, admin := range msp.admins {
		err = admin.Validate()
		if err != nil {
			return fmt.Errorf("admin %d is invalid, validation error %s", i, err)
		}
	}
	return nil
}
// GetType returns the type for this MSP
func (msp *bccspmsp) GetType() ProviderType {
	return FABRIC
}
// GetIdentifier returns the MSP identifier for this instance
func (msp *bccspmsp) GetIdentifier() (string, error) {
	return msp.name, nil
}
// GetTLSRootCerts returns the root certificates for this MSP
func (msp *bccspmsp) GetTLSRootCerts() [][]byte {
	return msp.tlsRootCerts
}
// GetTLSIntermediateCerts returns the intermediate root certificates for this MSP
func (msp *bccspmsp) GetTLSIntermediateCerts() [][]byte {
	return msp.tlsIntermediateCerts
}
// GetDefaultSigningIdentity returns the
// default signing identity for this MSP (if any)
func (msp *bccspmsp) GetDefaultSigningIdentity() (SigningIdentity, error) {
	mspLogger.Debugf("Obtaining default signing identity")
	if msp.signer == nil {
		return nil, fmt.Errorf("This MSP does not possess a valid default signing identity")
	}
	return msp.signer, nil
}
// GetSigningIdentity returns a specific signing
// identity identified by the supplied identifier
func (msp *bccspmsp) GetSigningIdentity(identifier *IdentityIdentifier) (SigningIdentity, error) {
	// TODO
	return nil, fmt.Errorf("No signing identity for %#v", identifier)
}
// Validate attempts to determine whether
// the supplied identity is valid according
// to this MSP's roots of trust; it returns
// nil in case the identity is valid or an
// error otherwise
func (msp *bccspmsp) Validate(id Identity) error {
	mspLogger.Debugf("MSP %s validating identity", msp.name)
	switch id := id.(type) {
	// If this identity is of this specific type,
	// this is how I can validate it given the
	// root of trust this MSP has
	case *identity:
		return msp.validateIdentity(id)
	default:
		return fmt.Errorf("Identity type not recognized")
	}
}
// DeserializeIdentity returns an Identity given the byte-level
// representation of a SerializedIdentity struct
func (msp *bccspmsp) DeserializeIdentity(serializedID []byte) (Identity, error) {
	mspLogger.Infof("Obtaining identity")
	// We first deserialize to a SerializedIdentity to get the MSP ID
	sId := &SerializedIdentity{} //SOURCE:m.SerializedIdentity
	err := proto.Unmarshal(serializedID, sId)
	if err != nil {
		return nil, fmt.Errorf("Could not deserialize a SerializedIdentity, err %s", err)
	}
	if sId.Mspid != msp.name {
		return nil, fmt.Errorf("Expected MSP ID %s, received %s", msp.name, sId.Mspid)
	}
	return msp.deserializeIdentityInternal(sId.IdBytes)
}
// deserializeIdentityInternal returns an identity given its byte-level representation
func (msp *bccspmsp) deserializeIdentityInternal(serializedIdentity []byte) (Identity, error) {
	// This MSP will always deserialize certs this way
	bl, _ := pem.Decode(serializedIdentity)
	if bl == nil {
		return nil, fmt.Errorf("Could not decode the PEM structure")
	}
	cert, err := x509.ParseCertificate(bl.Bytes)
	if err != nil {
		return nil, fmt.Errorf("ParseCertificate failed %s", err)
	}
	// Now we have the certificate; make sure that its fields
	// (e.g. the Issuer.OU or the Subject.OU) match with the
	// MSP id that this MSP has; otherwise it might be an attack
	// TODO!
	// We can't do it yet because there is no standardized way
	// (yet) to encode the MSP ID into the x.509 body of a cert
	// Use the hash of the identity's certificate as id in the IdentityIdentifier
	hashOpt, err := GetHashOpt(msp.cryptoConfig.IdentityIdentifierHashFunction) //SOURCE:bccsp.GetHashOpt
	if err != nil {
		return nil, fmt.Errorf("Failed getting hash function options [%s]", err)
	}
	digest, err := msp.bccsp.Hash(cert.Raw, hashOpt)
	if err != nil {
		return nil, fmt.Errorf("Failed hashing raw certificate to compute the id of the IdentityIdentifier [%s]", err)
	}
	id := &IdentityIdentifier{
		Mspid: msp.name,
		Id:    hex.EncodeToString(digest)}
	pub, err := msp.bccsp.KeyImport(cert, &X509PublicKeyImportOpts{Temporary: true}) //SOURCE:bccsp.X509PublicKeyImportOpts
	if err != nil {
		return nil, fmt.Errorf("Failed to import certitifacate's public key [%s]", err)
	}
	return newIdentity(id, cert, pub, msp)
}
// SatisfiesPrincipal returns null if the identity matches the principal or an error otherwise
func (msp *bccspmsp) SatisfiesPrincipal(id Identity, principal *MSPPrincipal) error { //SOURCE:m.MSPPrincipal
	switch principal.PrincipalClassification {
	// in this case, we have to check whether the
	// identity has a role in the msp - member or admin
	case MSPPrincipal_ROLE: //SOURCE:m.MSPPrincipal_ROLE
		// Principal contains the msp role
		mspRole := &MSPRole{} //SOURCE:m.MSPRole
		err := proto.Unmarshal(principal.Principal, mspRole)
		if err != nil {
			return fmt.Errorf("Could not unmarshal MSPRole from principal, err %s", err)
		}
		// at first, we check whether the MSP
		// identifier is the same as that of the identity
		if mspRole.MspIdentifier != msp.name {
			return fmt.Errorf("The identity is a member of a different MSP (expected %s, got %s)", mspRole.MspIdentifier, id.GetMSPIdentifier())
		}
		// now we validate the different msp roles
		switch mspRole.Role {
		case MSPRole_MEMBER: //SOURCE:m.MSPRole_MEMBER
			// in the case of member, we simply check
			// whether this identity is valid for the MSP
			mspLogger.Debugf("Checking if identity satisfies MEMBER role for %s", msp.name)
			return msp.Validate(id)
		case MSPRole_ADMIN: //SOURCE:m.MSPRole_ADMIN
			mspLogger.Debugf("Checking if identity satisfies ADMIN role for %s", msp.name)
			// in the case of admin, we check that the
			// id is exactly one of our admins
			for _, admincert := range msp.admins {
				if bytes.Equal(id.(*identity).cert.Raw, admincert.(*identity).cert.Raw) {
					// we do not need to check whether the admin is a valid identity
					// according to this MSP, since we already check this at Setup time
					// if there is a match, we can just return
					return nil
				}
			}
			return errors.New("This identity is not an admin")
		default:
			return fmt.Errorf("Invalid MSP role type %d", int32(mspRole.Role))
		}
	case MSPPrincipal_IDENTITY: //SOURCE:m.MSPPrincipal_IDENTITY
		// in this case we have to deserialize the principal's identity
		// and compare it byte-by-byte with our cert
		principalId, err := msp.DeserializeIdentity(principal.Principal)
		if err != nil {
			return fmt.Errorf("Invalid identity principal, not a certificate. Error %s", err)
		}
		if bytes.Equal(id.(*identity).cert.Raw, principalId.(*identity).cert.Raw) {
			return principalId.Validate()
		}
		return errors.New("The identities do not match")
	case MSPPrincipal_ORGANIZATION_UNIT: //SOURCE:m.MSPPrincipal_ORGANIZATION_UNIT
		// Principal contains the OrganizationUnit
		OU := &OrganizationUnit{} //SOURCE:m.OrganizationUnit
		err := proto.Unmarshal(principal.Principal, OU)
		if err != nil {
			return fmt.Errorf("Could not unmarshal OrganizationUnit from principal, err %s", err)
		}
		// at first, we check whether the MSP
		// identifier is the same as that of the identity
		if OU.MspIdentifier != msp.name {
			return fmt.Errorf("The identity is a member of a different MSP (expected %s, got %s)", OU.MspIdentifier, id.GetMSPIdentifier())
		}
		// we then check if the identity is valid with this MSP
		// and fail if it is not
		err = msp.Validate(id)
		if err != nil {
			return err
		}
		// now we check whether any of this identity's OUs match the requested one
		for _, ou := range id.GetOrganizationalUnits() {
			if ou.OrganizationalUnitIdentifier == OU.OrganizationalUnitIdentifier &&
				bytes.Equal(ou.CertifiersIdentifier, OU.CertifiersIdentifier) {
				return nil
			}
		}
		// if we are here, no match was found, return an error
		return errors.New("The identities do not match")
	default:
		return fmt.Errorf("Invalid principal type %d", int32(principal.PrincipalClassification))
	}
}
// getCertificationChain returns the certification chain of the passed identity within this msp
func (msp *bccspmsp) getCertificationChain(id Identity) ([]*x509.Certificate, error) {
	mspLogger.Debugf("MSP %s getting certification chain", msp.name)

	switch id := id.(type) {
	// If this identity is of this specific type,
	// this is how I can validate it given the
	// root of trust this MSP has
	case *identity:
		return msp.getCertificationChainForBCCSPIdentity(id)
	default:
		return nil, fmt.Errorf("Identity type not recognized")
	}
}
// getCertificationChainForBCCSPIdentity returns the certification chain of the passed bccsp identity within this msp
func (msp *bccspmsp) getCertificationChainForBCCSPIdentity(id *identity) ([]*x509.Certificate, error) {
	if id == nil {
		return nil, errors.New("Invalid bccsp identity. Must be different from nil.")
	}
	// we expect to have a valid VerifyOptions instance
	if msp.opts == nil {
		return nil, errors.New("Invalid msp instance")
	}
	// CAs cannot be directly used as identities..
	if id.cert.IsCA {
		return nil, errors.New("A CA certificate cannot be used directly by this MSP")
	}
	return msp.getValidationChain(id.cert, false)
}
func (msp *bccspmsp) getUniqueValidationChain(cert *x509.Certificate, opts x509.VerifyOptions) ([]*x509.Certificate, error) {
	// ask golang to validate the cert for us based on the options that we've built at setup time
	if msp.opts == nil {
		return nil, fmt.Errorf("The supplied identity has no verify options")
	}
	validationChains, err := cert.Verify(opts)
	if err != nil {
		return nil, fmt.Errorf("The supplied identity is not valid, Verify() returned %s", err)
	}
	// we only support a single validation chain;
	// if there's more than one then there might
	// be unclarity about who owns the identity
	if len(validationChains) != 1 {
		return nil, fmt.Errorf("This MSP only supports a single validation chain, got %d", len(validationChains))
	}
	return validationChains[0], nil
}
func (msp *bccspmsp) getValidationChain(cert *x509.Certificate, isIntermediateChain bool) ([]*x509.Certificate, error) {
	validationChain, err := msp.getUniqueValidationChain(cert, msp.getValidityOptsForCert(cert))
	if err != nil {
		return nil, fmt.Errorf("Failed getting validation chain %s", err)
	}
	// we expect a chain of length at least 2
	if len(validationChain) < 2 {
		return nil, fmt.Errorf("Expected a chain of length at least 2, got %d", len(validationChain))
	}
	// check that the parent is a leaf of the certification tree
	// if validating an intermediate chain, the first certificate will the parent
	parentPosition := 1
	if isIntermediateChain {
		parentPosition = 0
	}
	if msp.certificationTreeInternalNodesMap[string(validationChain[parentPosition].Raw)] {
		return nil, fmt.Errorf("Invalid validation chain. Parent certificate should be a leaf of the certification tree [%v].", cert.Raw)
	}
	return validationChain, nil
}
// getCertificationChainIdentifier returns the certification chain identifier of the passed identity within this msp.
// The identifier is computes as the SHA256 of the concatenation of the certificates in the chain.
func (msp *bccspmsp) getCertificationChainIdentifier(id Identity) ([]byte, error) {
	chain, err := msp.getCertificationChain(id)
	if err != nil {
		return nil, fmt.Errorf("Failed getting certification chain for [%v]: [%s]", id, err)
	}
	// chain[0] is the certificate representing the identity.
	// It will be discarded
	return msp.getCertificationChainIdentifierFromChain(chain[1:])
}
func (msp *bccspmsp) getCertificationChainIdentifierFromChain(chain []*x509.Certificate) ([]byte, error) {
	// Hash the chain
	// Use the hash of the identity's certificate as id in the IdentityIdentifier
	hashOpt, err := GetHashOpt(msp.cryptoConfig.IdentityIdentifierHashFunction) //SOURCE:bccsp.GetHashOpt
	if err != nil {
		return nil, fmt.Errorf("Failed getting hash function options [%s]", err)
	}
	hf, err := msp.bccsp.GetHash(hashOpt)
	if err != nil {
		return nil, fmt.Errorf("Failed getting hash function when computing certification chain identifier: [%s]", err)
	}
	for i := 0; i < len(chain); i++ {
		hf.Write(chain[i].Raw)
	}
	return hf.Sum(nil), nil
}
func (msp *bccspmsp) setupCrypto(conf *FabricMSPConfig) error { //SOURCE:m.FabricMSPConfig
	msp.cryptoConfig = conf.CryptoConfig
	if msp.cryptoConfig == nil {
		// Move to defaults
		msp.cryptoConfig = &FabricCryptoConfig{ //SOURCE:m.FabricCryptoConfig
			SignatureHashFamily:            SHA2, //SOURCE:bccsp.SHA2
			IdentityIdentifierHashFunction: SHA256, //SOURCE:bccsp.SHA256
		}
		mspLogger.Debugf("CryptoConfig was nil. Move to defaults.")
	}
	if msp.cryptoConfig.SignatureHashFamily == "" {
		msp.cryptoConfig.SignatureHashFamily = SHA2 //SOURCE:bccsp.SHA2
		mspLogger.Debugf("CryptoConfig.SignatureHashFamily was nil. Move to defaults.")
	}
	if msp.cryptoConfig.IdentityIdentifierHashFunction == "" {
		msp.cryptoConfig.IdentityIdentifierHashFunction = SHA256 //SOURCE:bccsp.SHA256
		mspLogger.Debugf("CryptoConfig.IdentityIdentifierHashFunction was nil. Move to defaults.")
	}
	return nil
}
func (msp *bccspmsp) setupCAs(conf *FabricMSPConfig) error { //SOURCE:m.FabricMSPConfig
	// make and fill the set of CA certs - we expect them to be there
	if len(conf.RootCerts) == 0 {
		return errors.New("Expected at least one CA certificate")
	}
	// pre-create the verify options with roots and intermediates.
	// This is needed to make certificate sanitation working.
	// Recall that sanitization is applied also to root CA and intermediate
	// CA certificates. After their sanitization is done, the opts
	// will be recreated using the sanitized certs.
	msp.opts = &x509.VerifyOptions{Roots: x509.NewCertPool(), Intermediates: x509.NewCertPool()}
	for _, v := range conf.RootCerts {
		cert, err := msp.getCertFromPem(v)
		if err != nil {
			return err
		}
		msp.opts.Roots.AddCert(cert)
	}
	for _, v := range conf.IntermediateCerts {
		cert, err := msp.getCertFromPem(v)
		if err != nil {
			return err
		}
		msp.opts.Intermediates.AddCert(cert)
	}
	// Load root and intermediate CA identities
	// Recall that when an identity is created, its certificate gets sanitized
	msp.rootCerts = make([]Identity, len(conf.RootCerts))
	for i, trustedCert := range conf.RootCerts {
		id, _, err := msp.getIdentityFromConf(trustedCert)
		if err != nil {
			return err
		}
		msp.rootCerts[i] = id
	}
	// make and fill the set of intermediate certs (if present)
	msp.intermediateCerts = make([]Identity, len(conf.IntermediateCerts))
	for i, trustedCert := range conf.IntermediateCerts {
		id, _, err := msp.getIdentityFromConf(trustedCert)
		if err != nil {
			return err
		}
		msp.intermediateCerts[i] = id
	}
	// root CA and intermediate CA certificates are sanitized, they can be reimported
	msp.opts = &x509.VerifyOptions{Roots: x509.NewCertPool(), Intermediates: x509.NewCertPool()}
	for _, id := range msp.rootCerts {
		msp.opts.Roots.AddCert(id.(*identity).cert)
	}
	for _, id := range msp.intermediateCerts {
		msp.opts.Intermediates.AddCert(id.(*identity).cert)
	}
	// make and fill the set of admin certs (if present)
	msp.admins = make([]Identity, len(conf.Admins))
	for i, admCert := range conf.Admins {
		id, _, err := msp.getIdentityFromConf(admCert)
		if err != nil {
			return err
		}
		msp.admins[i] = id
	}
	return nil
}
func (msp *bccspmsp) setupAdmins(conf *FabricMSPConfig) error { //SOURCE:m.FabricMSPConfig
	// make and fill the set of admin certs (if present)
	msp.admins = make([]Identity, len(conf.Admins))
	for i, admCert := range conf.Admins {
		id, _, err := msp.getIdentityFromConf(admCert)
		if err != nil {
			return err
		}
		msp.admins[i] = id
	}
	return nil
}
func (msp *bccspmsp) setupCRLs(conf *FabricMSPConfig) error { //SOURCE:m.FabricMSPConfig
	// setup the CRL (if present)
	msp.CRL = make([]*pkix.CertificateList, len(conf.RevocationList))
	for i, crlbytes := range conf.RevocationList {
		crl, err := x509.ParseCRL(crlbytes)
		if err != nil {
			return fmt.Errorf("Could not parse RevocationList, err %s", err)
		}
		// TODO: pre-verify the signature on the CRL and create a map
		//       of CA certs to respective CRLs so that later upon
		//       validation we can already look up the CRL given the
		//       chain of the certificate to be validated
		msp.CRL[i] = crl
	}
	return nil
}
func (msp *bccspmsp) finalizeSetupCAs(config *FabricMSPConfig) error { //SOURCE:m.FabricMSPConfig
	// ensure that our CAs are properly formed and that they are valid
	for _, id := range append(append([]Identity{}, msp.rootCerts...), msp.intermediateCerts...) {
		if !isCACert(id.(*identity).cert) {
			return fmt.Errorf("CA Certificate did not have the Subject Key Identifier extension, (SN: %s)", id.(*identity).cert.SerialNumber)
		}
		if err := msp.validateCAIdentity(id.(*identity)); err != nil {
			return fmt.Errorf("CA Certificate is not valid, (SN: %s) [%s]", id.(*identity).cert.SerialNumber, err)
		}
	}
	// populate certificationTreeInternalNodesMap to mark the internal nodes of the
	// certification tree
	msp.certificationTreeInternalNodesMap = make(map[string]bool)
	for _, id := range append([]Identity{}, msp.intermediateCerts...) {
		chain, err := msp.getUniqueValidationChain(id.(*identity).cert, msp.getValidityOptsForCert(id.(*identity).cert))
		if err != nil {
			return fmt.Errorf("Failed getting validation chain, (SN: %s)", id.(*identity).cert.SerialNumber)
		}
		// Recall chain[0] is id.(*identity).id so it does not count as a parent
		for i := 1; i < len(chain); i++ {
			msp.certificationTreeInternalNodesMap[string(chain[i].Raw)] = true
		}
	}
	return nil
}
func (msp *bccspmsp) setupSigningIdentity(conf *FabricMSPConfig) error { //SOURCE:m.FabricMSPConfig
	if conf.SigningIdentity != nil {
		sid, err := msp.getSigningIdentityFromConf(conf.SigningIdentity)
		if err != nil {
			return err
		}
		msp.signer = sid
	}
	return nil
}
func (msp *bccspmsp) setupOUs(conf *FabricMSPConfig) error { //SOURCE:m.FabricMSPConfig
	msp.ouIdentifiers = make(map[string][][]byte)
	for _, ou := range conf.OrganizationalUnitIdentifiers {
		// 1. check that certificate is registered in msp.rootCerts or msp.intermediateCerts
		cert, err := msp.getCertFromPem(ou.Certificate)
		if err != nil {
			return fmt.Errorf("Failed getting certificate for [%v]: [%s]", ou, err)
		}
		// 2. Sanitize it to ensure like for like comparison
		cert, err = msp.sanitizeCert(cert)
		if err != nil {
			return fmt.Errorf("sanitizeCert failed %s", err)
		}
		found := false
		root := false
		// Search among root certificates
		for _, v := range msp.rootCerts {
			if v.(*identity).cert.Equal(cert) {
				found = true
				root = true
				break
			}
		}
		if !found {
			// Search among root intermediate certificates
			for _, v := range msp.intermediateCerts {
				if v.(*identity).cert.Equal(cert) {
					found = true
					break
				}
			}
		}
		if !found {
			// Certificate not valid, reject configuration
			return fmt.Errorf("Failed adding OU. Certificate [%v] not in root or intermediate certs.", ou.Certificate)
		}
		// 3. get the certification path for it
		var certifiersIdentitifer []byte
		var chain []*x509.Certificate
		if root {
			chain = []*x509.Certificate{cert}
		} else {
			chain, err = msp.getValidationChain(cert, true)
			if err != nil {
				return fmt.Errorf("Failed computing validation chain for [%v]. [%s]", cert, err)
			}
		}
		// 4. compute the hash of the certification path
		certifiersIdentitifer, err = msp.getCertificationChainIdentifierFromChain(chain)
		if err != nil {
			return fmt.Errorf("Failed computing Certifiers Identifier for [%v]. [%s]", ou.Certificate, err)
		}
		// Check for duplicates
		found = false
		for _, id := range msp.ouIdentifiers[ou.OrganizationalUnitIdentifier] {
			if bytes.Equal(id, certifiersIdentitifer) {
				mspLogger.Warningf("Duplicate found in ou identifiers [%s, %v]", ou.OrganizationalUnitIdentifier, id)
				found = true
				break
			}
		}
		if !found {
			// No duplicates found, add it
			msp.ouIdentifiers[ou.OrganizationalUnitIdentifier] = append(
				msp.ouIdentifiers[ou.OrganizationalUnitIdentifier],
				certifiersIdentitifer,
			)
		}
	}
	return nil
}
func (msp *bccspmsp) setupTLSCAs(conf *FabricMSPConfig) error { //SOURCE:m.FabricMSPConfig
	opts := &x509.VerifyOptions{Roots: x509.NewCertPool(), Intermediates: x509.NewCertPool()}
	// Load TLS root and intermediate CA identities
	msp.tlsRootCerts = make([][]byte, len(conf.TlsRootCerts))
	rootCerts := make([]*x509.Certificate, len(conf.TlsRootCerts))
	for i, trustedCert := range conf.TlsRootCerts {
		cert, err := msp.getCertFromPem(trustedCert)
		if err != nil {
			return err
		}
		rootCerts[i] = cert
		msp.tlsRootCerts[i] = trustedCert
		opts.Roots.AddCert(cert)
	}
	// make and fill the set of intermediate certs (if present)
	msp.tlsIntermediateCerts = make([][]byte, len(conf.TlsIntermediateCerts))
	intermediateCerts := make([]*x509.Certificate, len(conf.TlsIntermediateCerts))
	for i, trustedCert := range conf.TlsIntermediateCerts {
		cert, err := msp.getCertFromPem(trustedCert)
		if err != nil {
			return err
		}
		intermediateCerts[i] = cert
		msp.tlsIntermediateCerts[i] = trustedCert
		opts.Intermediates.AddCert(cert)
	}
	// ensure that our CAs are properly formed and that they are valid
	for _, cert := range append(append([]*x509.Certificate{}, rootCerts...), intermediateCerts...) {
		if cert == nil {
			continue
		}
		if !isCACert(cert) {
			return fmt.Errorf("CA Certificate did not have the Subject Key Identifier extension, (SN: %s)", cert.SerialNumber)
		}
		if err := msp.validateTLSCAIdentity(cert, opts); err != nil {
			return fmt.Errorf("CA Certificate is not valid, (SN: %s) [%s]", cert.SerialNumber, err)
		}
	}
	return nil
}
// sanitizeCert ensures that x509 certificates signed using ECDSA
// do have signatures in Low-S. If this is not the case, the certificate
// is regenerated to have a Low-S signature.
func (msp *bccspmsp) sanitizeCert(cert *x509.Certificate) (*x509.Certificate, error) {
	if isECDSASignedCert(cert) {
		// Lookup for a parent certificate to perform the sanitization
		var parentCert *x509.Certificate
		if cert.IsCA {
			// at this point, cert might be a root CA certificate
			// or an intermediate CA certificate
			chain, err := msp.getUniqueValidationChain(cert, msp.getValidityOptsForCert(cert))
			if err != nil {
				return nil, err
			}
			if len(chain) == 1 {
				// cert is a root CA certificate
				parentCert = cert
			} else {
				// cert is an intermediate CA certificate
				parentCert = chain[1]
			}
		} else {
			chain, err := msp.getUniqueValidationChain(cert, msp.getValidityOptsForCert(cert))
			if err != nil {
				return nil, err
			}
			parentCert = chain[1]
		}
		// Sanitize
		var err error
		cert, err = sanitizeECDSASignedCert(cert, parentCert)
		if err != nil {
			return nil, err
		}
	}
	return cert, nil
}
func (msp *bccspmsp) validateIdentity(id *identity) error {
	validationChain, err := msp.getCertificationChainForBCCSPIdentity(id)
	if err != nil {
		return fmt.Errorf("Could not obtain certification chain, err %s", err)
	}
	err = msp.validateIdentityAgainstChain(id, validationChain)
	if err != nil {
		return fmt.Errorf("Could not validate identity against certification chain, err %s", err)
	}
	err = msp.validateIdentityOUs(id)
	if err != nil {
		return fmt.Errorf("Could not validate identity's OUs, err %s", err)
	}
	return nil
}
func (msp *bccspmsp) validateCAIdentity(id *identity) error {
	if !id.cert.IsCA {
		return errors.New("Only CA identities can be validated")
	}
	validationChain, err := msp.getUniqueValidationChain(id.cert, msp.getValidityOptsForCert(id.cert))
	if err != nil {
		return fmt.Errorf("Could not obtain certification chain, err %s", err)
	}
	if len(validationChain) == 1 {
		// validationChain[0] is the root CA certificate
		return nil
	}
	return msp.validateIdentityAgainstChain(id, validationChain)
}
func (msp *bccspmsp) validateTLSCAIdentity(cert *x509.Certificate, opts *x509.VerifyOptions) error {
	if !cert.IsCA {
		return errors.New("Only CA identities can be validated")
	}
	validationChain, err := msp.getUniqueValidationChain(cert, *opts)
	if err != nil {
		return fmt.Errorf("Could not obtain certification chain, err %s", err)
	}
	if len(validationChain) == 1 {
		// validationChain[0] is the root CA certificate
		return nil
	}
	return msp.validateCertAgainstChain(cert, validationChain)
}
func (msp *bccspmsp) validateIdentityAgainstChain(id *identity, validationChain []*x509.Certificate) error {
	return msp.validateCertAgainstChain(id.cert, validationChain)
}
func (msp *bccspmsp) validateCertAgainstChain(cert *x509.Certificate, validationChain []*x509.Certificate) error {
	// here we know that the identity is valid; now we have to check whether it has been revoked
	// identify the SKI of the CA that signed this cert
	SKI, err := getSubjectKeyIdentifierFromCert(validationChain[1])
	if err != nil {
		return fmt.Errorf("Could not obtain Subject Key Identifier for signer cert, err %s", err)
	}
	// check whether one of the CRLs we have has this cert's
	// SKI as its AuthorityKeyIdentifier
	for _, crl := range msp.CRL {
		aki, err := getAuthorityKeyIdentifierFromCrl(crl)
		if err != nil {
			return fmt.Errorf("Could not obtain Authority Key Identifier for crl, err %s", err)
		}
		// check if the SKI of the cert that signed us matches the AKI of any of the CRLs
		if bytes.Equal(aki, SKI) {
			// we have a CRL, check whether the serial number is revoked
			for _, rc := range crl.TBSCertList.RevokedCertificates {
				if rc.SerialNumber.Cmp(cert.SerialNumber) == 0 {
					// We have found a CRL whose AKI matches the SKI of
					// the CA (root or intermediate) that signed the
					// certificate that is under validation. As a
					// precaution, we verify that said CA is also the
					// signer of this CRL.
					err = validationChain[1].CheckCRLSignature(crl)
					if err != nil {
						// the CA cert that signed the certificate
						// that is under validation did not sign the
						// candidate CRL - skip
						mspLogger.Warningf("Invalid signature over the identified CRL, error %s", err)
						continue
					}
					// A CRL also includes a time of revocation so that
					// the CA can say "this cert is to be revoked starting
					// from this time"; however here we just assume that
					// revocation applies instantaneously from the time
					// the MSP config is committed and used so we will not
					// make use of that field
					return errors.New("The certificate has been revoked")
				}
			}
		}
	}
	return nil
}
func (msp *bccspmsp) validateIdentityOUs(id *identity) error {
	// Check that the identity's OUs are compatible with those recognized by this MSP,
	// meaning that the intersection is not empty.
	if len(msp.ouIdentifiers) > 0 {
		found := false
		for _, OU := range id.GetOrganizationalUnits() {
			certificationIDs, exists := msp.ouIdentifiers[OU.OrganizationalUnitIdentifier]
			if exists {
				for _, certificationID := range certificationIDs {
					if bytes.Equal(certificationID, OU.CertifiersIdentifier) {
						found = true
						break
					}
				}
			}
		}
		if !found {
			if len(id.GetOrganizationalUnits()) == 0 {
				return fmt.Errorf("The identity certificate does not contain an Organizational Unit (OU)")
			}
			return fmt.Errorf("None of the identity's organizational units [%v] are in MSP %s", id.GetOrganizationalUnits(), msp.name)
		}
	}
	return nil
}
func (msp *bccspmsp) getValidityOptsForCert(cert *x509.Certificate) x509.VerifyOptions {
	// First copy the opts to override the CurrentTime field
	// in order to make the certificate passing the expiration test
	// independently from the real local current time.
	// This is a temporary workaround for FAB-3678
	var tempOpts x509.VerifyOptions
	tempOpts.Roots = msp.opts.Roots
	tempOpts.DNSName = msp.opts.DNSName
	tempOpts.Intermediates = msp.opts.Intermediates
	tempOpts.KeyUsages = msp.opts.KeyUsages
	tempOpts.CurrentTime = cert.NotBefore.Add(time.Second)
	return tempOpts
}

/*** fabric/common/cauthdsl/cauthdsl_builder.go ***/
// AcceptAllPolicy always evaluates to true
var AcceptAllPolicy *SignaturePolicyEnvelope //SOURCE:cb.SignaturePolicyEnvelope
// SignedBy creates a SignaturePolicy requiring a given signer's signature
func SignedBy(index int32) *SignaturePolicy { //SOURCE:cb.SignaturePolicy
	return &SignaturePolicy{ //SOURCE:cb.SignaturePolicy
		Type: &SignaturePolicy_SignedBy{ //SOURCE:cb.SignaturePolicy_SignedBy
			SignedBy: index,
		},
	}
}
// SignedByMspMember creates a SignaturePolicyEnvelope
// requiring 1 signature from any member of the specified MSP
func SignedByMspMember(mspId string) *SignaturePolicyEnvelope { //SOURCE:cb.SignaturePolicyEnvelope
	// specify the principal: it's a member of the msp we just found
	principal := &MSPPrincipal{ //SOURCE:msp.MSPPrincipal
		PrincipalClassification: MSPPrincipal_ROLE, //SOURCE:msp.MSPPrincipal_ROLE
		Principal:               MarshalOrPanic(&MSPRole{Role: MSPRole_MEMBER, MspIdentifier: mspId})} //SOURCE:utils.MarshalOrPanic //SOURCE:msp.MSPRole //SOURCE:msp.MSPRole_MEMBER
	// create the policy: it requires exactly 1 signature from the first (and only) principal
	p := &SignaturePolicyEnvelope{ //SOURCE:cb.SignaturePolicyEnvelope
		Version:    0,
		Rule:       NOutOf(1, []*SignaturePolicy{SignedBy(0)}), //SOURCE:cb.SignaturePolicy
		Identities: []*MSPPrincipal{principal}, //SOURCE:msp.MSPPrincipal
	}
	return p
}
// SignedByMspAdmin creates a SignaturePolicyEnvelope
// requiring 1 signature from any admin of the specified MSP
func SignedByMspAdmin(mspId string) *SignaturePolicyEnvelope { //SOURCE:cb.SignaturePolicyEnvelope
	// specify the principal: it's a member of the msp we just found
	principal := &MSPPrincipal{ //SOURCE:msp.MSPPrincipal
		PrincipalClassification: MSPPrincipal_ROLE, //SOURCE:msp.MSPPrincipal_ROLE
		Principal:               MarshalOrPanic(&MSPRole{Role: MSPRole_ADMIN, MspIdentifier: mspId})} //SOURCE:utils.MarshalOrPanic //SOURCE:msp.MSPRole //SOURCE:MSPRole //SOURCE:MSPRole_ADMIN
	// create the policy: it requires exactly 1 signature from the first (and only) principal
	p := &SignaturePolicyEnvelope{ //SOURCE:cb.SignaturePolicyEnvelope
		Version:    0,
		Rule:       NOutOf(1, []*SignaturePolicy{SignedBy(0)}), //SOURCE:cb.SignaturePolicy
		Identities: []*MSPPrincipal{principal}, //SOURCE:msp.MSPPrincipal
	}
	return p
}
// NOutOf creates a policy which requires N out of the slice of policies to evaluate to true
func NOutOf(n int32, policies []*SignaturePolicy) *SignaturePolicy { //SOURCE:cb.SignaturePolicy
	return &SignaturePolicy{ //SOURCE:cb.SignaturePolicy
		Type: &SignaturePolicy_NOutOf_{ //SOURCE:cb.SignaturePolicy_NOutOf_
			NOutOf: &SignaturePolicy_NOutOf{ //SOURCE:cb.SignaturePolicy_NOutOf
				N:     n,
				Rules: policies,
			},
		},
	}
}

/*** fabric/common/config/msp/config_util.go ***/
// ReadersPolicyKey is the key used for the read policy
const ReadersPolicyKey = "Readers"
// WritersPolicyKey is the key used for the read policy
const WritersPolicyKey = "Writers"
// AdminsPolicyKey is the key used for the read policy
const AdminsPolicyKey = "Admins"
// TemplateGroupMSPWithAdminRolePrincipal creates an MSP ConfigValue at the given configPath with Admin policy
// of role type ADMIN if admin==true or MEMBER otherwise
func TemplateGroupMSPWithAdminRolePrincipal(configPath []string, mspConfig *MSPConfig, admin bool) *ConfigGroup { //SOURCE:mspprotos.MSPConfig //SOURCE:cb.ConfigGroup
	// check that the type for that MSP is supported
	if mspConfig.Type != int32(FABRIC) { //SOURCE:msp.FABRIC
		logger.Panicf("Setup error: unsupported msp type %d", mspConfig.Type)
	}
	// create the msp instance
	mspInst, err := NewBccspMsp() //SOURCE:msp.NewBccspMsp
	if err != nil {
		logger.Panicf("Creating the MSP manager failed, err %s", err)
	}
	// set it up
	err = mspInst.Setup(mspConfig)
	if err != nil {
		logger.Panicf("Setting up the MSP manager failed, err %s", err)
	}
	// add the MSP to the map of pending MSPs
	mspID, _ := mspInst.GetIdentifier()
	memberPolicy := &ConfigPolicy{ //SOURCE:cb.ConfigPolicy
		Policy: &Policy{ //SOURCE:cb.Policy
			Type:  int32(Policy_SIGNATURE), //SOURCE:cb.Policy_SIGNATURE
			Value: MarshalOrPanic(SignedByMspMember(mspID)), //SOURCE:utils.MarshalOrPanic //SOURCE:cauthdsl.SignedByMspMember
		},
	}
	var adminSigPolicy []byte
	if admin {
		adminSigPolicy = MarshalOrPanic(SignedByMspAdmin(mspID)) //SOURCE:utils.MarshalOrPanic //SOURCE:cauthdsl.SignedByMspAdmin
	} else {
		adminSigPolicy = MarshalOrPanic(SignedByMspMember(mspID)) //SOURCE:utils.MarshalOrPanic //SOURCE:cauthdsl.SignedByMspMember
	}
	adminPolicy := &ConfigPolicy{ //SOURCE:cb.ConfigPolicy
		Policy: &Policy{ //SOURCE:cb.Policy
			Type:  int32(Policy_SIGNATURE), //SOURCE:cb.Policy_SIGNATURE
			Value: adminSigPolicy,
		},
	}
	result := NewConfigGroup() //SOURCE:cb.NewConfigGroup
	intermediate := result
	for _, group := range configPath {
		intermediate.Groups[group] = NewConfigGroup() //SOURCE:cb.NewConfigGroup
		intermediate = intermediate.Groups[group]
	}
	intermediate.Values[MSPKey] = &ConfigValue{ //SOURCE:cb.ConfigValue
		Value: MarshalOrPanic(mspConfig), //SOURCE:utils.MarshalOrPanic
	}
	intermediate.Policies[AdminsPolicyKey] = adminPolicy
	intermediate.Policies[ReadersPolicyKey] = memberPolicy
	intermediate.Policies[WritersPolicyKey] = memberPolicy
	return result
}

/*** fabric/protos/orderer/configuration.pb.go ***/
type ConsensusType struct {
	Type string `protobuf:"bytes,1,opt,name=type" json:"type,omitempty"`
}
func (m *ConsensusType) Reset()                    { *m = ConsensusType{} }
func (m *ConsensusType) String() string            { return proto.CompactTextString(m) }
func (*ConsensusType) ProtoMessage()               {}
func (*ConsensusType) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{0} }
func (m *ConsensusType) GetType() string {
	if m != nil {
		return m.Type
	}
	return ""
}
type BatchSizeORDERER struct { //WAS:BatchSize
	// Simply specified as number of messages for now, in the future
	// we may want to allow this to be specified by size in bytes
	MaxMessageCount uint32 `protobuf:"varint,1,opt,name=max_message_count,json=maxMessageCount" json:"max_message_count,omitempty"`
	// The byte count of the serialized messages in a batch cannot
	// exceed this value.
	AbsoluteMaxBytes uint32 `protobuf:"varint,2,opt,name=absolute_max_bytes,json=absoluteMaxBytes" json:"absolute_max_bytes,omitempty"`
	// The byte count of the serialized messages in a batch should not
	// exceed this value.
	PreferredMaxBytes uint32 `protobuf:"varint,3,opt,name=preferred_max_bytes,json=preferredMaxBytes" json:"preferred_max_bytes,omitempty"`
}
func (m *BatchSizeORDERER) Reset()                    { *m = BatchSizeORDERER{} } //WAS:BatchSize
func (m *BatchSizeORDERER) String() string            { return proto.CompactTextString(m) } //WAS:BatchSize
func (*BatchSizeORDERER) ProtoMessage()               {} //WAS:BatchSize
func (*BatchSizeORDERER) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{1} } //WAS:BatchSize
func (m *BatchSizeORDERER) GetMaxMessageCount() uint32 { //WAS:BatchSize
	if m != nil {
		return m.MaxMessageCount
	}
	return 0
}
func (m *BatchSizeORDERER) GetAbsoluteMaxBytes() uint32 { //WAS:BatchSize
	if m != nil {
		return m.AbsoluteMaxBytes
	}
	return 0
}
func (m *BatchSizeORDERER) GetPreferredMaxBytes() uint32 { //WAS:BatchSize
	if m != nil {
		return m.PreferredMaxBytes
	}
	return 0
}
type BatchTimeout struct {
	// Any duration string parseable by ParseDuration():
	// https://golang.org/pkg/time/#ParseDuration
	Timeout string `protobuf:"bytes,1,opt,name=timeout" json:"timeout,omitempty"`
}
func (m *BatchTimeout) Reset()                    { *m = BatchTimeout{} }
func (m *BatchTimeout) String() string            { return proto.CompactTextString(m) }
func (*BatchTimeout) ProtoMessage()               {}
func (*BatchTimeout) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{2} }
func (m *BatchTimeout) GetTimeout() string {
	if m != nil {
		return m.Timeout
	}
	return ""
}
// Carries a list of bootstrap brokers, i.e. this is not the exclusive set of
// brokers an ordering service
type KafkaBrokers struct {
	// Each broker here should be identified using the (IP|host):port notation,
	// e.g. 127.0.0.1:7050, or localhost:7050 are valid entries
	Brokers []string `protobuf:"bytes,1,rep,name=brokers" json:"brokers,omitempty"`
}
func (m *KafkaBrokers) Reset()                    { *m = KafkaBrokers{} }
func (m *KafkaBrokers) String() string            { return proto.CompactTextString(m) }
func (*KafkaBrokers) ProtoMessage()               {}
func (*KafkaBrokers) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{3} }
func (m *KafkaBrokers) GetBrokers() []string {
	if m != nil {
		return m.Brokers
	}
	return nil
}
// ChannelRestrictions is the mssage which conveys restrictions on channel creation for an orderer
type ChannelRestrictions struct {
	MaxCount uint64 `protobuf:"varint,1,opt,name=max_count,json=maxCount" json:"max_count,omitempty"`
}
func (m *ChannelRestrictions) Reset()                    { *m = ChannelRestrictions{} }
func (m *ChannelRestrictions) String() string            { return proto.CompactTextString(m) }
func (*ChannelRestrictions) ProtoMessage()               {}
func (*ChannelRestrictions) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{4} }
func (m *ChannelRestrictions) GetMaxCount() uint64 {
	if m != nil {
		return m.MaxCount
	}
	return 0
}

/*** fabric/common/config/organization.go ***/
type OrganizationProtos struct {
	MSP *MSPConfig //SOURCE:mspprotos.MSPConfig
}
type OrganizationConfig struct {
	*standardValues
	protos *OrganizationProtos
	organizationGroup *OrganizationGroup
	msp   MSP //SOURCE:msp.MSP
	mspID string
}
// Config stores common configuration information for organizations
type OrganizationGroup struct {
	*ProposerCONFIG //WAS:Proposer
	*OrganizationConfig
	name             string
	mspConfigHandler *MSPConfigHandler //SOURCE:mspconfig.MSPConfigHandler
}
// NewConfig creates an instnace of the organization Config
func NewOrganizationGroup(name string, mspConfigHandler *MSPConfigHandler) *OrganizationGroup { //SOURCE:mspconfig.MSPConfigHandler
	og := &OrganizationGroup{
		name:             name,
		mspConfigHandler: mspConfigHandler,
	}
	og.ProposerCONFIG = NewProposer(og) //WAS:Proposer
	return og
}
// Name returns the name this org is referred to in config
func (og *OrganizationGroup) Name() string {
	return og.name
}
// MSPID returns the MSP ID associated with this org
func (og *OrganizationGroup) MSPID() string {
	return og.mspID
}
// NewGroup always errors
func (og *OrganizationGroup) NewGroup(name string) (ValueProposer, error) {
	return nil, fmt.Errorf("Organization does not support subgroups")
}
// Allocate creates the proto resources neeeded for a proposal
func (og *OrganizationGroup) Allocate() Values {
	return NewOrganizationConfig(og)
}
func NewOrganizationConfig(og *OrganizationGroup) *OrganizationConfig {
	oc := &OrganizationConfig{
		protos: &OrganizationProtos{},
		organizationGroup: og,
	}
	var err error
	oc.standardValues, err = NewStandardValues(oc.protos)
	if err != nil {
		logger.Panicf("Programming error: %s", err)
	}
	return oc
}
// Validate returns whether the configuration is valid
func (oc *OrganizationConfig) Validate(tx interface{}, groups map[string]ValueProposer) error {
	return oc.validateMSP(tx)
}
func (oc *OrganizationConfig) Commit() {
	oc.organizationGroup.OrganizationConfig = oc
}
func (oc *OrganizationConfig) validateMSP(tx interface{}) error {
	var err error
	logger.Debugf("Setting up MSP for org %s", oc.organizationGroup.name)
	oc.msp, err = oc.organizationGroup.mspConfigHandler.ProposeMSP(tx, oc.protos.MSP)
	if err != nil {
		return err
	}
	oc.mspID, _ = oc.msp.GetIdentifier()
	if oc.mspID == "" {
		return fmt.Errorf("MSP for org %s has empty MSP ID", oc.organizationGroup.name)
	}
	if oc.organizationGroup.OrganizationConfig != nil && oc.organizationGroup.mspID != oc.mspID {
		return fmt.Errorf("Organization %s attempted to change its MSP ID from %s to %s", oc.organizationGroup.name, oc.organizationGroup.mspID, oc.mspID)
	}
	return nil
}

/*** fabric/common/config/orderer.go ***/
const (
	// OrdererGroupKey is the group name for the orderer config
	OrdererGroupKey = "Orderer"
)
const (
	// ConsensusTypeKey is the cb.ConfigItem type key name for the ConsensusType message
	ConsensusTypeKey = "ConsensusType"
	// BatchSizeKey is the cb.ConfigItem type key name for the BatchSize message
	BatchSizeKey = "BatchSize"
	// BatchTimeoutKey is the cb.ConfigItem type key name for the BatchTimeout message
	BatchTimeoutKey = "BatchTimeout"
	// ChannelRestrictions is the key name for the ChannelRestrictions message
	ChannelRestrictionsKey = "ChannelRestrictions"
	// KafkaBrokersKey is the cb.ConfigItem type key name for the KafkaBrokers message
	KafkaBrokersKey = "KafkaBrokers"
)
// OrdererProtos is used as the source of the OrdererConfig
type OrdererProtos struct {
	ConsensusType       *ConsensusType //SOURCE:ab.ConsensusType
	BatchSize           *BatchSizeORDERER //WAS:BatchSize //SOURCE:ab.BatchSize
	BatchTimeout        *BatchTimeout //SOURCE:ab.BatchTimeout
	KafkaBrokers        *KafkaBrokers //SOURCE:ab.KafkaBrokers
	ChannelRestrictions *ChannelRestrictions //SOURCE:ab.ChannelRestrictions
}
// Config is stores the orderer component configuration
type OrdererGroup struct {
	*ProposerCONFIG //WAS:Proposer
	*OrdererConfig
	mspConfig *MSPConfigHandler //SOURCE:msp.MSPConfigHandler
}
// NewConfig creates a new *OrdererConfig
func NewOrdererGroup(mspConfig *MSPConfigHandler) *OrdererGroup { //SOURCE:msp.MSPConfigHandler
	og := &OrdererGroup{
		mspConfig: mspConfig,
	}
	og.ProposerCONFIG = NewProposer(og) //WAS:Proposer
	return og
}
// NewGroup returns an Org instance
func (og *OrdererGroup) NewGroup(name string) (ValueProposer, error) {
	return NewOrganizationGroup(name, og.mspConfig), nil
}
func (og *OrdererGroup) Allocate() Values {
	return NewOrdererConfig(og)
}
// OrdererConfig holds the orderer configuration information
type OrdererConfig struct {
	*standardValues
	protos       *OrdererProtos
	ordererGroup *OrdererGroup
	orgs         map[string]Org
	batchTimeout time.Duration
}
// NewOrdererConfig creates a new instance of the orderer config
func NewOrdererConfig(og *OrdererGroup) *OrdererConfig {
	oc := &OrdererConfig{
		protos:       &OrdererProtos{},
		ordererGroup: og,
	}
	var err error
	oc.standardValues, err = NewStandardValues(oc.protos)
	if err != nil {
		logger.Panicf("Programming error: %s", err)
	}
	return oc
}
// Commit writes the orderer config back to the orderer config group
func (oc *OrdererConfig) Commit() {
	oc.ordererGroup.OrdererConfig = oc
}
// ConsensusType returns the configured consensus type
func (oc *OrdererConfig) ConsensusType() string {
	return oc.protos.ConsensusType.Type
}
// BatchSize returns the maximum number of messages to include in a block
func (oc *OrdererConfig) BatchSize() *BatchSizeORDERER { //WAS:BatchSize //SOURCE:ab.BatchSize
	return oc.protos.BatchSize
}
// BatchTimeout returns the amount of time to wait before creating a batch
func (oc *OrdererConfig) BatchTimeout() time.Duration {
	return oc.batchTimeout
}
// KafkaBrokers returns the addresses (IP:port notation) of a set of "bootstrap"
// Kafka brokers, i.e. this is not necessarily the entire set of Kafka brokers
// used for ordering
func (oc *OrdererConfig) KafkaBrokers() []string {
	return oc.protos.KafkaBrokers.Brokers
}
// MaxChannelsCount returns the maximum count of channels this orderer supports
func (oc *OrdererConfig) MaxChannelsCount() uint64 {
	return oc.protos.ChannelRestrictions.MaxCount
}
// Organizations returns a map of the orgs in the channel
func (oc *OrdererConfig) Organizations() map[string]Org {
	return oc.orgs
}
func (oc *OrdererConfig) Validate(tx interface{}, groups map[string]ValueProposer) error {
	for _, validator := range []func() error{
		oc.validateConsensusType,
		oc.validateBatchSize,
		oc.validateBatchTimeout,
		oc.validateKafkaBrokers,
	} {
		if err := validator(); err != nil {
			return err
		}
	}
	var ok bool
	oc.orgs = make(map[string]Org)
	for key, value := range groups {
		oc.orgs[key], ok = value.(*OrganizationGroup)
		if !ok {
			return fmt.Errorf("Organization sub-group %s was not an OrgGroup, actually %T", key, value)
		}
	}
	return nil
}
func (oc *OrdererConfig) validateConsensusType() error {
	if oc.ordererGroup.OrdererConfig != nil && oc.ordererGroup.ConsensusType() != oc.protos.ConsensusType.Type {
		// The first config we accept the consensus type regardless
		return fmt.Errorf("Attempted to change the consensus type from %s to %s after init", oc.ordererGroup.ConsensusType(), oc.protos.ConsensusType.Type)
	}
	return nil
}
func (oc *OrdererConfig) validateBatchSize() error {
	if oc.protos.BatchSize.MaxMessageCount == 0 {
		return fmt.Errorf("Attempted to set the batch size max message count to an invalid value: 0")
	}
	if oc.protos.BatchSize.AbsoluteMaxBytes == 0 {
		return fmt.Errorf("Attempted to set the batch size absolute max bytes to an invalid value: 0")
	}
	if oc.protos.BatchSize.PreferredMaxBytes == 0 {
		return fmt.Errorf("Attempted to set the batch size preferred max bytes to an invalid value: 0")
	}
	if oc.protos.BatchSize.PreferredMaxBytes > oc.protos.BatchSize.AbsoluteMaxBytes {
		return fmt.Errorf("Attempted to set the batch size preferred max bytes (%v) greater than the absolute max bytes (%v).", oc.protos.BatchSize.PreferredMaxBytes, oc.protos.BatchSize.AbsoluteMaxBytes)
	}
	return nil
}
func (oc *OrdererConfig) validateBatchTimeout() error {
	var err error
	oc.batchTimeout, err = time.ParseDuration(oc.protos.BatchTimeout.Timeout)
	if err != nil {
		return fmt.Errorf("Attempted to set the batch timeout to a invalid value: %s", err)
	}
	if oc.batchTimeout <= 0 {
		return fmt.Errorf("Attempted to set the batch timeout to a non-positive value: %s", oc.batchTimeout)
	}
	return nil
}
func (oc *OrdererConfig) validateKafkaBrokers() error {
	for _, broker := range oc.protos.KafkaBrokers.Brokers {
		if !brokerEntrySeemsValid(broker) {
			return fmt.Errorf("Invalid broker entry: %s", broker)
		}
	}
	return nil
}
// This does just a barebones sanity check.
func brokerEntrySeemsValid(broker string) bool {
	if !strings.Contains(broker, ":") {
		return false
	}
	parts := strings.Split(broker, ":")
	if len(parts) > 2 {
		return false
	}
	host := parts[0]
	port := parts[1]
	if _, err := strconv.ParseUint(port, 10, 16); err != nil {
		return false
	}
	// Valid hostnames may contain only the ASCII letters 'a' through 'z' (in a
	// case-insensitive manner), the digits '0' through '9', and the hyphen. IP
	// v4 addresses are  represented in dot-decimal notation, which consists of
	// four decimal numbers, each ranging from 0 to 255, separated by dots,
	// e.g., 172.16.254.1
	// The following regular expression:
	// 1. allows just a-z (case-insensitive), 0-9, and the dot and hyphen characters
	// 2. does not allow leading trailing dots or hyphens
	re, _ := regexp.Compile("^([a-zA-Z0-9]|[a-zA-Z0-9][a-zA-Z0-9.-]*[a-zA-Z0-9])$")
	matched := re.FindString(host)
	return len(matched) == len(host)
}

/*** fabric/common/config/orderer_util.go ***/
func ordererConfigGroup(key string, value []byte) *ConfigGroup { //SOURCE:cb.ConfigGroup
	result := NewConfigGroup() //SOURCE:cb.NewConfigGroup
	result.Groups[OrdererGroupKey] = NewConfigGroup() //SOURCE:cb.NewConfigGroup
	result.Groups[OrdererGroupKey].Values[key] = &ConfigValue{ //SOURCE:cb.ConfigValue
		Value: value,
	}
	return result
}
// TemplateConsensusType creates a headerless config item representing the consensus type
func TemplateConsensusType(typeValue string) *ConfigGroup { //SOURCE:cb.ConfigGroup
	return ordererConfigGroup(ConsensusTypeKey, MarshalOrPanic(&ConsensusType{Type: typeValue})) //SOURCE:utils.MarshalOrPanic //SOURCE:ab.ConsensusType
}
// TemplateBatchSize creates a headerless config item representing the batch size
func TemplateBatchSize(batchSize *BatchSizeORDERER) *ConfigGroup { //WAS:BatchSize //SOURCE:cb.ConfigGroup
	return ordererConfigGroup(BatchSizeKey, MarshalOrPanic(batchSize)) //SOURCE:utils.MarshalOrPanic
}
// TemplateBatchTimeout creates a headerless config item representing the batch timeout
func TemplateBatchTimeout(batchTimeout string) *ConfigGroup { //SOURCE:cb.ConfigGroup
	return ordererConfigGroup(BatchTimeoutKey, MarshalOrPanic(&BatchTimeout{Timeout: batchTimeout})) //SOURCE:utils.MarshalOrPanic //SOURCE:ab.BatchTimeout
}
// TemplateChannelRestrictions creates a config group with ChannelRestrictions specified
func TemplateChannelRestrictions(maxChannels uint64) *ConfigGroup { //SOURCE:cb.ConfigGroup
	return ordererConfigGroup(ChannelRestrictionsKey, MarshalOrPanic(&ChannelRestrictions{MaxCount: maxChannels})) //SOURCE:utils.MarshalOrPanic //SOURCE:ab.ChannelRestrictions
}
// TemplateKafkaBrokers creates a headerless config item representing the kafka brokers
func TemplateKafkaBrokers(brokers []string) *ConfigGroup { //SOURCE:cb.ConfigGroup
	return ordererConfigGroup(KafkaBrokersKey, MarshalOrPanic(&KafkaBrokers{Brokers: brokers})) //SOURCE:utils.MarshalOrPanic //SOURCE:ab.KafkaBrokers
}

/*** fabric/protos/msp/msp_config.pb.go ***/
// MSPConfig collects all the configuration information for
// an MSP. The Config field should be unmarshalled in a way
// that depends on the Type
type MSPConfig struct {
	// Type holds the type of the MSP; the default one would
	// be of type FABRIC implementing an X.509 based provider
	Type int32 `protobuf:"varint,1,opt,name=type" json:"type,omitempty"`
	// Config is MSP dependent configuration info
	Config []byte `protobuf:"bytes,2,opt,name=config,proto3" json:"config,omitempty"`
}
func (m *MSPConfig) Reset()                    { *m = MSPConfig{} }
func (m *MSPConfig) String() string            { return proto.CompactTextString(m) }
func (*MSPConfig) ProtoMessage()               {}
func (*MSPConfig) Descriptor() ([]byte, []int) { return fileDescriptor1MSP, []int{0} } //WAS:fileDescriptor1
func (m *MSPConfig) GetType() int32 {
	if m != nil {
		return m.Type
	}
	return 0
}
func (m *MSPConfig) GetConfig() []byte {
	if m != nil {
		return m.Config
	}
	return nil
}
// FabricMSPConfig collects all the configuration information for
// a Fabric MSP.
// Here we assume a default certificate validation policy, where
// any certificate signed by any of the listed rootCA certs would
// be considered as valid under this MSP.
// This MSP may or may not come with a signing identity. If it does,
// it can also issue signing identities. If it does not, it can only
// be used to validate and verify certificates.
type FabricMSPConfig struct {
	// Name holds the identifier of the MSP; MSP identifier
	// is chosen by the application that governs this MSP.
	// For example, and assuming the default implementation of MSP,
	// that is X.509-based and considers a single Issuer,
	// this can refer to the Subject OU field or the Issuer OU field.
	Name string `protobuf:"bytes,1,opt,name=name" json:"name,omitempty"`
	// List of root certificates trusted by this MSP
	// they are used upon certificate validation (see
	// comment for IntermediateCerts below)
	RootCerts [][]byte `protobuf:"bytes,2,rep,name=root_certs,json=rootCerts,proto3" json:"root_certs,omitempty"`
	// List of intermediate certificates trusted by this MSP;
	// they are used upon certificate validation as follows:
	// validation attempts to build a path from the certificate
	// to be validated (which is at one end of the path) and
	// one of the certs in the RootCerts field (which is at
	// the other end of the path). If the path is longer than
	// 2, certificates in the middle are searched within the
	// IntermediateCerts pool
	IntermediateCerts [][]byte `protobuf:"bytes,3,rep,name=intermediate_certs,json=intermediateCerts,proto3" json:"intermediate_certs,omitempty"`
	// Identity denoting the administrator of this MSP
	Admins [][]byte `protobuf:"bytes,4,rep,name=admins,proto3" json:"admins,omitempty"`
	// Identity revocation list
	RevocationList [][]byte `protobuf:"bytes,5,rep,name=revocation_list,json=revocationList,proto3" json:"revocation_list,omitempty"`
	// SigningIdentity holds information on the signing identity
	// this peer is to use, and which is to be imported by the
	// MSP defined before
	SigningIdentity *SigningIdentityInfo `protobuf:"bytes,6,opt,name=signing_identity,json=signingIdentity" json:"signing_identity,omitempty"`
	// OrganizationalUnitIdentifiers holds one or more
	// fabric organizational unit identifiers that belong to
	// this MSP configuration
	OrganizationalUnitIdentifiers []*FabricOUIdentifier `protobuf:"bytes,7,rep,name=organizational_unit_identifiers,json=organizationalUnitIdentifiers" json:"organizational_unit_identifiers,omitempty"`
	// FabricCryptoConfig contains the configuration parameters
	// for the cryptographic algorithms used by this MSP
	CryptoConfig *FabricCryptoConfig `protobuf:"bytes,8,opt,name=crypto_config,json=cryptoConfig" json:"crypto_config,omitempty"`
	// List of TLS root certificates trusted by this MSP.
	// They are returned by GetTLSRootCerts.
	TlsRootCerts [][]byte `protobuf:"bytes,9,rep,name=tls_root_certs,json=tlsRootCerts,proto3" json:"tls_root_certs,omitempty"`
	// List of TLS intermediate certificates trusted by this MSP;
	// They are returned by GetTLSIntermediateCerts.
	TlsIntermediateCerts [][]byte `protobuf:"bytes,10,rep,name=tls_intermediate_certs,json=tlsIntermediateCerts,proto3" json:"tls_intermediate_certs,omitempty"`
}
func (m *FabricMSPConfig) Reset()                    { *m = FabricMSPConfig{} }
func (m *FabricMSPConfig) String() string            { return proto.CompactTextString(m) }
func (*FabricMSPConfig) ProtoMessage()               {}
func (*FabricMSPConfig) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{1} }
func (m *FabricMSPConfig) GetName() string {
	if m != nil {
		return m.Name
	}
	return ""
}
func (m *FabricMSPConfig) GetRootCerts() [][]byte {
	if m != nil {
		return m.RootCerts
	}
	return nil
}
func (m *FabricMSPConfig) GetIntermediateCerts() [][]byte {
	if m != nil {
		return m.IntermediateCerts
	}
	return nil
}
func (m *FabricMSPConfig) GetAdmins() [][]byte {
	if m != nil {
		return m.Admins
	}
	return nil
}
func (m *FabricMSPConfig) GetRevocationList() [][]byte {
	if m != nil {
		return m.RevocationList
	}
	return nil
}
func (m *FabricMSPConfig) GetSigningIdentity() *SigningIdentityInfo {
	if m != nil {
		return m.SigningIdentity
	}
	return nil
}
func (m *FabricMSPConfig) GetOrganizationalUnitIdentifiers() []*FabricOUIdentifier {
	if m != nil {
		return m.OrganizationalUnitIdentifiers
	}
	return nil
}
func (m *FabricMSPConfig) GetCryptoConfig() *FabricCryptoConfig {
	if m != nil {
		return m.CryptoConfig
	}
	return nil
}
func (m *FabricMSPConfig) GetTlsRootCerts() [][]byte {
	if m != nil {
		return m.TlsRootCerts
	}
	return nil
}
func (m *FabricMSPConfig) GetTlsIntermediateCerts() [][]byte {
	if m != nil {
		return m.TlsIntermediateCerts
	}
	return nil
}
// FabricCryptoConfig contains configuration parameters
// for the cryptographic algorithms used by the MSP
// this configuration refers to
type FabricCryptoConfig struct {
	// SignatureHashFamily is a string representing the hash family to be used
	// during sign and verify operations.
	// Allowed values are "SHA2" and "SHA3".
	SignatureHashFamily string `protobuf:"bytes,1,opt,name=signature_hash_family,json=signatureHashFamily" json:"signature_hash_family,omitempty"`
	// IdentityIdentifierHashFunction is a string representing the hash function
	// to be used during the computation of the identity identifier of an MSP identity.
	// Allowed values are "SHA256", "SHA384" and "SHA3_256", "SHA3_384".
	IdentityIdentifierHashFunction string `protobuf:"bytes,2,opt,name=identity_identifier_hash_function,json=identityIdentifierHashFunction" json:"identity_identifier_hash_function,omitempty"`
}
func (m *FabricCryptoConfig) Reset()                    { *m = FabricCryptoConfig{} }
func (m *FabricCryptoConfig) String() string            { return proto.CompactTextString(m) }
func (*FabricCryptoConfig) ProtoMessage()               {}
func (*FabricCryptoConfig) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{2} }
func (m *FabricCryptoConfig) GetSignatureHashFamily() string {
	if m != nil {
		return m.SignatureHashFamily
	}
	return ""
}
func (m *FabricCryptoConfig) GetIdentityIdentifierHashFunction() string {
	if m != nil {
		return m.IdentityIdentifierHashFunction
	}
	return ""
}
// SigningIdentityInfo represents the configuration information
// related to the signing identity the peer is to use for generating
// endorsements
type SigningIdentityInfo struct {
	// PublicSigner carries the public information of the signing
	// identity. For an X.509 provider this would be represented by
	// an X.509 certificate
	PublicSigner []byte `protobuf:"bytes,1,opt,name=public_signer,json=publicSigner,proto3" json:"public_signer,omitempty"`
	// PrivateSigner denotes a reference to the private key of the
	// peer's signing identity
	PrivateSigner *KeyInfo `protobuf:"bytes,2,opt,name=private_signer,json=privateSigner" json:"private_signer,omitempty"`
}
func (m *SigningIdentityInfo) Reset()                    { *m = SigningIdentityInfo{} }
func (m *SigningIdentityInfo) String() string            { return proto.CompactTextString(m) }
func (*SigningIdentityInfo) ProtoMessage()               {}
func (*SigningIdentityInfo) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{3} }
func (m *SigningIdentityInfo) GetPublicSigner() []byte {
	if m != nil {
		return m.PublicSigner
	}
	return nil
}
func (m *SigningIdentityInfo) GetPrivateSigner() *KeyInfo {
	if m != nil {
		return m.PrivateSigner
	}
	return nil
}
// KeyInfo represents a (secret) key that is either already stored
// in the bccsp/keystore or key material to be imported to the
// bccsp key-store. In later versions it may contain also a
// keystore identifier
type KeyInfo struct {
	// Identifier of the key inside the default keystore; this for
	// the case of Software BCCSP as well as the HSM BCCSP would be
	// the SKI of the key
	KeyIdentifier string `protobuf:"bytes,1,opt,name=key_identifier,json=keyIdentifier" json:"key_identifier,omitempty"`
	// KeyMaterial (optional) for the key to be imported; this is
	// properly encoded key bytes, prefixed by the type of the key
	KeyMaterial []byte `protobuf:"bytes,2,opt,name=key_material,json=keyMaterial,proto3" json:"key_material,omitempty"`
}
func (m *KeyInfo) Reset()                    { *m = KeyInfo{} }
func (m *KeyInfo) String() string            { return proto.CompactTextString(m) }
func (*KeyInfo) ProtoMessage()               {}
func (*KeyInfo) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{4} }
func (m *KeyInfo) GetKeyIdentifier() string {
	if m != nil {
		return m.KeyIdentifier
	}
	return ""
}
func (m *KeyInfo) GetKeyMaterial() []byte {
	if m != nil {
		return m.KeyMaterial
	}
	return nil
}
// FabricOUIdentifier represents an organizational unit and
// its related chain of trust identifier.
type FabricOUIdentifier struct {
	// Certificate represents the second certificate in a certification chain.
	// (Notice that the first certificate in a certification chain is supposed
	// to be the certificate of an identity).
	// It must correspond to the certificate of root or intermediate CA
	// recognized by the MSP this message belongs to.
	// Starting from this certificate, a certification chain is computed
	// and boud to the OrganizationUnitIdentifier specified
	Certificate []byte `protobuf:"bytes,1,opt,name=certificate,proto3" json:"certificate,omitempty"`
	// OrganizationUnitIdentifier defines the organizational unit under the
	// MSP identified with MSPIdentifier
	OrganizationalUnitIdentifier string `protobuf:"bytes,2,opt,name=organizational_unit_identifier,json=organizationalUnitIdentifier" json:"organizational_unit_identifier,omitempty"`
}
func (m *FabricOUIdentifier) Reset()                    { *m = FabricOUIdentifier{} }
func (m *FabricOUIdentifier) String() string            { return proto.CompactTextString(m) }
func (*FabricOUIdentifier) ProtoMessage()               {}
func (*FabricOUIdentifier) Descriptor() ([]byte, []int) { return fileDescriptor1, []int{5} }
func (m *FabricOUIdentifier) GetCertificate() []byte {
	if m != nil {
		return m.Certificate
	}
	return nil
}
func (m *FabricOUIdentifier) GetOrganizationalUnitIdentifier() string {
	if m != nil {
		return m.OrganizationalUnitIdentifier
	}
	return ""
}
var fileDescriptor1MSP = []byte{ //WAS:fileDescriptor1
	// 599 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x09, 0x6e, 0x88, 0x02, 0xff, 0x7c, 0x54, 0xdf, 0x6e, 0xd3, 0x3c,
	0x14, 0x57, 0xd7, 0xad, 0xfb, 0x7a, 0x9a, 0x76, 0xfb, 0xbc, 0x31, 0x72, 0xc1, 0x46, 0x16, 0x40,
	0xe4, 0x86, 0x54, 0xda, 0x90, 0xb8, 0xe1, 0x6a, 0x45, 0x13, 0x15, 0x54, 0x4c, 0xa9, 0x76, 0xc3,
	0x4d, 0xe4, 0xa6, 0x4e, 0x6a, 0x35, 0xb1, 0x23, 0xdb, 0x9d, 0x14, 0xc4, 0x5b, 0xf0, 0xaa, 0x3c,
	0x00, 0x8a, 0xed, 0xb6, 0x29, 0x4c, 0xbb, 0xb3, 0x7f, 0x7f, 0x4e, 0x8f, 0x7f, 0xe7, 0x34, 0x70,
	0x5a, 0xc8, 0x72, 0x58, 0xc8, 0x32, 0x4e, 0x38, 0x4b, 0x69, 0x16, 0x96, 0x82, 0x2b, 0x8e, 0xda,
	0x85, 0x2c, 0xfd, 0x0f, 0xd0, 0x9d, 0x4c, 0xef, 0x46, 0x1a, 0x47, 0x08, 0xf6, 0x55, 0x55, 0x12,
	0xb7, 0xe5, 0xb5, 0x82, 0x83, 0x48, 0x9f, 0xd1, 0x19, 0x74, 0x8c, 0xcb, 0xdd, 0xf3, 0x5a, 0x81,
	0x13, 0xd9, 0x9b, 0xff, 0xbb, 0x0d, 0x47, 0xb7, 0x78, 0x26, 0x68, 0xb2, 0xe3, 0x67, 0xb8, 0x30,
	0xfe, 0x6e, 0xa4, 0xcf, 0xe8, 0x1c, 0x40, 0x70, 0xae, 0xe2, 0x84, 0x08, 0x25, 0xdd, 0x3d, 0xaf,
	0x1d, 0x38, 0x51, 0xb7, 0x46, 0x46, 0x35, 0x80, 0xde, 0x01, 0xa2, 0x4c, 0x11, 0x51, 0x90, 0x39,
	0xc5, 0x8a, 0x58, 0x59, 0x5b, 0xcb, 0xfe, 0x6f, 0x32, 0x46, 0x7e, 0x06, 0x1d, 0x3c, 0x2f, 0x28,
	0x93, 0xee, 0xbe, 0x96, 0xd8, 0x1b, 0x7a, 0x0b, 0x47, 0x82, 0x3c, 0xf0, 0x04, 0x2b, 0xca, 0x59,
	0x9c, 0x53, 0xa9, 0xdc, 0x03, 0x2d, 0x18, 0x6c, 0xe1, 0xaf, 0x54, 0x2a, 0x34, 0x82, 0x63, 0x49,
	0x33, 0x46, 0x59, 0x16, 0xd3, 0x39, 0x61, 0x8a, 0xaa, 0xca, 0xed, 0x78, 0xad, 0xa0, 0x77, 0xe5,
	0x86, 0x85, 0x2c, 0xc3, 0xa9, 0x21, 0xc7, 0x96, 0x1b, 0xb3, 0x94, 0x47, 0x47, 0x72, 0x17, 0x44,
	0x31, 0xbc, 0xe4, 0x22, 0xc3, 0x8c, 0xfe, 0xd0, 0x85, 0x71, 0x1e, 0xaf, 0x18, 0x55, 0xb6, 0x60,
	0x4a, 0x89, 0x90, 0xee, 0xa1, 0xd7, 0x0e, 0x7a, 0x57, 0xcf, 0x75, 0x4d, 0x13, 0xd3, 0xb7, 0xfb,
	0xf1, 0x86, 0x8f, 0xce, 0x77, 0xfd, 0xf7, 0x8c, 0xaa, 0x2d, 0x2b, 0xd1, 0x47, 0xe8, 0x27, 0xa2,
	0x2a, 0x15, 0xb7, 0x13, 0x73, 0xff, 0xd3, 0x2d, 0x36, 0xcb, 0x8d, 0x34, 0x6f, 0x82, 0x8f, 0x9c,
	0xa4, 0x71, 0x43, 0xaf, 0x61, 0xa0, 0x72, 0x19, 0x37, 0x62, 0xef, 0xea, 0x2c, 0x1c, 0x95, 0xcb,
	0x68, 0x93, 0xfc, 0x7b, 0x38, 0xab, 0x55, 0x8f, 0xa4, 0x0f, 0x5a, 0x7d, 0xaa, 0x72, 0x39, 0xfe,
	0x7b, 0x00, 0xfe, 0xaf, 0x16, 0xa0, 0x7f, 0x1b, 0x40, 0x57, 0xf0, 0xac, 0x0e, 0x09, 0xab, 0x95,
	0x20, 0xf1, 0x02, 0xcb, 0x45, 0x9c, 0xe2, 0x82, 0xe6, 0x95, 0x5d, 0x85, 0x93, 0x0d, 0xf9, 0x19,
	0xcb, 0xc5, 0xad, 0xa6, 0xd0, 0x18, 0x2e, 0xd7, 0x23, 0x68, 0x44, 0x67, 0xdd, 0x2b, 0x96, 0xd4,
	0xd1, 0xe8, 0xa5, 0xeb, 0x46, 0x17, 0x6b, 0xe1, 0x36, 0x24, 0x5d, 0xc8, 0xaa, 0x7c, 0x0e, 0x27,
	0x8f, 0x0c, 0x0e, 0xbd, 0x82, 0x7e, 0xb9, 0x9a, 0xe5, 0x34, 0x89, 0xeb, 0xdf, 0x27, 0x42, 0x77,
	0xe3, 0x44, 0x8e, 0x01, 0xa7, 0x1a, 0x43, 0xd7, 0x30, 0x28, 0x05, 0x7d, 0xa8, 0x9f, 0x6f, 0x55,
	0x7b, 0x3a, 0x6c, 0x47, 0x87, 0xfd, 0x85, 0x98, 0x1d, 0xe8, 0x5b, 0x8d, 0x31, 0xf9, 0x53, 0x38,
	0xb4, 0x0c, 0x7a, 0x03, 0x83, 0x25, 0x69, 0xbe, 0xc0, 0xbe, 0xb9, 0xbf, 0x24, 0x8d, 0x76, 0xd1,
	0x25, 0x38, 0xb5, 0xac, 0xc0, 0x8a, 0x08, 0x8a, 0x73, 0xfb, 0x6f, 0xea, 0x2d, 0x49, 0x35, 0xb1,
	0x90, 0xff, 0x73, 0x1d, 0x6d, 0x73, 0x55, 0x90, 0x07, 0xbd, 0x7a, 0x2c, 0x34, 0xa5, 0x09, 0x56,
	0xc4, 0x3e, 0xa1, 0x09, 0xa1, 0x4f, 0x70, 0xf1, 0xf4, 0x3a, 0xda, 0x14, 0x5f, 0x3c, 0xb5, 0x74,
	0x37, 0x31, 0x5c, 0x72, 0x91, 0x85, 0x8b, 0xaa, 0x24, 0x22, 0x27, 0xf3, 0x8c, 0x88, 0x30, 0xd5,
	0xdd, 0x98, 0xcf, 0x85, 0xac, 0xe3, 0xb8, 0x39, 0x9e, 0xc8, 0xd2, 0x8c, 0xfc, 0x0e, 0x27, 0x4b,
	0x9c, 0x91, 0xef, 0x41, 0x46, 0xd5, 0x62, 0x35, 0x0b, 0x13, 0x5e, 0x0c, 0x1b, 0xde, 0xa1, 0xf1,
	0x0e, 0x8d, 0xb7, 0xfe, 0xf8, 0xcc, 0x3a, 0xfa, 0x7c, 0xfd, 0x27, 0x00, 0x00, 0xff, 0xff, 0x2e,
	0xb1, 0x83, 0xaa, 0x8e, 0x04, 0x00, 0x00,
}

/*** fabric/msp/configbuilder.go ***/
type OrganizationalUnitIdentifiersConfiguration struct {
	Certificate                  string `yaml:"Certificate,omitempty"`
	OrganizationalUnitIdentifier string `yaml:"OrganizationalUnitIdentifier,omitempty"`
}
type Configuration struct {
	OrganizationalUnitIdentifiers []*OrganizationalUnitIdentifiersConfiguration `yaml:"OrganizationalUnitIdentifiers,omitempty"`
}
func readFile(file string) ([]byte, error) {
	fileCont, err := ioutil.ReadFile(file)
	if err != nil {
		return nil, fmt.Errorf("Could not read file %s, err %s", file, err)
	}
	return fileCont, nil
}
func readPemFile(file string) ([]byte, error) {
	bytes, err := readFile(file)
	if err != nil {
		return nil, err
	}
	b, _ := pem.Decode(bytes)
	if b == nil { // TODO: also check that the type is what we expect (cert vs key..)
		return nil, fmt.Errorf("No pem content for file %s", file)
	}
	return bytes, nil
}
func getPemMaterialFromDir(dir string) ([][]byte, error) {
	mspLogger.Debugf("Reading directory %s", dir)
	_, err := os.Stat(dir)
	if os.IsNotExist(err) {
		return nil, err
	}
	content := make([][]byte, 0)
	files, err := ioutil.ReadDir(dir)
	if err != nil {
		return nil, fmt.Errorf("Could not read directory %s, err %s", err, dir)
	}
	for _, f := range files {
		if f.IsDir() {
			continue
		}
		fullName := filepath.Join(dir, string(filepath.Separator), f.Name())
		mspLogger.Debugf("Inspecting file %s", fullName)
		item, err := readPemFile(fullName)
		if err != nil {
			mspLogger.Warningf("Failed readgin file %s: %s", fullName, err)
			continue
		}
		content = append(content, item)
	}
	return content, nil
}
const (
	cacerts              = "cacerts"
	admincerts           = "admincerts"
	signcerts            = "signcerts"
	keystore             = "keystore"
	intermediatecerts    = "intermediatecerts"
	crlsfolder           = "crls"
	configfilename       = "config.yaml"
	tlscacerts           = "tlscacerts"
	tlsintermediatecerts = "tlsintermediatecerts"
)
func GetVerifyingMspConfig(dir string, ID string) (*MSPConfig, error) { //SOURCE:msp.MSPConfig
	return getMspConfig(dir, ID, nil)
}
func getMspConfig(dir string, ID string, sigid *SigningIdentityInfo) (*MSPConfig, error) { //SOURCE:msp.SigningIdentityInfo //SOURCE:msp.MSPConfig
	cacertDir := filepath.Join(dir, cacerts)
	admincertDir := filepath.Join(dir, admincerts)
	intermediatecertsDir := filepath.Join(dir, intermediatecerts)
	crlsDir := filepath.Join(dir, crlsfolder)
	configFile := filepath.Join(dir, configfilename)
	tlscacertDir := filepath.Join(dir, tlscacerts)
	tlsintermediatecertsDir := filepath.Join(dir, tlsintermediatecerts)
	cacerts, err := getPemMaterialFromDir(cacertDir)
	if err != nil || len(cacerts) == 0 {
		return nil, fmt.Errorf("Could not load a valid ca certificate from directory %s, err %s", cacertDir, err)
	}
	admincert, err := getPemMaterialFromDir(admincertDir)
	if err != nil || len(admincert) == 0 {
		return nil, fmt.Errorf("Could not load a valid admin certificate from directory %s, err %s", admincertDir, err)
	}
	intermediatecerts, err := getPemMaterialFromDir(intermediatecertsDir)
	if os.IsNotExist(err) {
		mspLogger.Debugf("Intermediate certs folder not found at [%s]. Skipping. [%s]", intermediatecertsDir, err)
	} else if err != nil {
		return nil, fmt.Errorf("Failed loading intermediate ca certs at [%s]: [%s]", intermediatecertsDir, err)
	}
	tlsCACerts, err := getPemMaterialFromDir(tlscacertDir)
	tlsIntermediateCerts := [][]byte{}
	if os.IsNotExist(err) {
		mspLogger.Debugf("TLS CA certs folder not found at [%s]. Skipping and ignoring TLS intermediate CA folder. [%s]", tlsintermediatecertsDir, err)
	} else if err != nil {
		return nil, fmt.Errorf("Failed loading TLS ca certs at [%s]: [%s]", tlsintermediatecertsDir, err)
	} else if len(tlsCACerts) != 0 {
		tlsIntermediateCerts, err = getPemMaterialFromDir(tlsintermediatecertsDir)
		if os.IsNotExist(err) {
			mspLogger.Debugf("TLS intermediate certs folder not found at [%s]. Skipping. [%s]", tlsintermediatecertsDir, err)
		} else if err != nil {
			return nil, fmt.Errorf("Failed loading TLS intermediate ca certs at [%s]: [%s]", tlsintermediatecertsDir, err)
		}
	} else {
		mspLogger.Debugf("TLS CA certs folder at [%s] is empty. Skipping.", tlsintermediatecertsDir)
	}
	crls, err := getPemMaterialFromDir(crlsDir)
	if os.IsNotExist(err) {
		mspLogger.Debugf("crls folder not found at [%s]. Skipping. [%s]", crlsDir, err)
	} else if err != nil {
		return nil, fmt.Errorf("Failed loading crls at [%s]: [%s]", crlsDir, err)
	}
	// Load configuration file
	// if the configuration file is there then load it
	// otherwise skip it
	var ouis []*FabricOUIdentifier //SOURCE:msp.FabricOUIdentifier
	_, err = os.Stat(configFile)
	if err == nil {
		// load the file, if there is a failure in loading it then
		// return an error
		raw, err := ioutil.ReadFile(configFile)
		if err != nil {
			return nil, fmt.Errorf("Failed loading configuration file at [%s]: [%s]", configFile, err)
		}
		configuration := Configuration{}
		err = yaml.Unmarshal(raw, &configuration)
		if err != nil {
			return nil, fmt.Errorf("Failed unmarshalling configuration file at [%s]: [%s]", configFile, err)
		}
		// Prepare OrganizationalUnitIdentifiers
		if len(configuration.OrganizationalUnitIdentifiers) > 0 {
			for _, ouID := range configuration.OrganizationalUnitIdentifiers {
				f := filepath.Join(dir, ouID.Certificate)
				raw, err = ioutil.ReadFile(f)
				if err != nil {
					return nil, fmt.Errorf("Failed loading OrganizationalUnit certificate at [%s]: [%s]", f, err)
				}
				oui := &FabricOUIdentifier{ //SOURCE:msp.FabricOUIdentifier
					Certificate:                  raw,
					OrganizationalUnitIdentifier: ouID.OrganizationalUnitIdentifier,
				}
				ouis = append(ouis, oui)
			}
		}
	} else {
		mspLogger.Debugf("MSP configuration file not found at [%s]: [%s]", configFile, err)
	}
	// Set FabricCryptoConfig
	cryptoConfig := &FabricCryptoConfig{ //SOURCE:msp.FabricCryptoConfig
		SignatureHashFamily:            SHA2, //SOURCE:bccsp.SHA2
		IdentityIdentifierHashFunction: SHA256, //SOURCE:bccsp.SHA256
	}
	// Compose FabricMSPConfig
	fmspconf := &FabricMSPConfig{ //SOURCE:msp.FabricMSPConfig
		Admins:            admincert,
		RootCerts:         cacerts,
		IntermediateCerts: intermediatecerts,
		SigningIdentity:   sigid,
		Name:              ID,
		OrganizationalUnitIdentifiers: ouis,
		RevocationList:                crls,
		CryptoConfig:                  cryptoConfig,
		TlsRootCerts:                  tlsCACerts,
		TlsIntermediateCerts:          tlsIntermediateCerts,
	}
	fmpsjs, _ := proto.Marshal(fmspconf)
	mspconf := &MSPConfig{Config: fmpsjs, Type: int32(FABRIC)}  //SOURCE:msp.MSPConfig
	return mspconf, nil
}

/*** fabric/common/config/application.go ***/
// ApplicationGroupKey is the group name for the Application config
const ApplicationGroupKey = "Application"
// ApplicationGroup represents the application config group
type ApplicationGroup struct {
	*ProposerCONFIG //WAS:Proposer
	*ApplicationConfig
	mspConfig *MSPConfigHandler //SOURCE:msp.MSPConfigHandler
}
type ApplicationConfig struct {
	*standardValues
	applicationGroup *ApplicationGroup
	applicationOrgs  map[string]ApplicationOrg
}
// NewSharedConfigImpl creates a new SharedConfigImpl with the given CryptoHelper
func NewApplicationGroup(mspConfig *MSPConfigHandler) *ApplicationGroup { //SOURCE:msp.MSPConfigHandler
	ag := &ApplicationGroup{
		mspConfig: mspConfig,
	}
	ag.ProposerCONFIG = NewProposer(ag) //WAS:Proposer
	return ag
}
func (ag *ApplicationGroup) NewGroup(name string) (ValueProposer, error) {
	return NewApplicationOrgGroup(name, ag.mspConfig), nil
}
// Allocate returns a new instance of the ApplicationConfig
func (ag *ApplicationGroup) Allocate() Values {
	return NewApplicationConfig(ag)
}
func NewApplicationConfig(ag *ApplicationGroup) *ApplicationConfig {
	sv, err := NewStandardValues(&(struct{}{}))
	if err != nil {
		logger.Panicf("Programming error: %s", err)
	}
	return &ApplicationConfig{
		applicationGroup: ag,
		// Currently there are no config values
		standardValues: sv,
	}
}
func (ac *ApplicationConfig) Validate(tx interface{}, groups map[string]ValueProposer) error {
	ac.applicationOrgs = make(map[string]ApplicationOrg)
	var ok bool
	for key, value := range groups {
		ac.applicationOrgs[key], ok = value.(*ApplicationOrgGroup)
		if !ok {
			return fmt.Errorf("Application sub-group %s was not an ApplicationOrgGroup, actually %T", key, value)
		}
	}
	return nil
}
func (ac *ApplicationConfig) Commit() {
	ac.applicationGroup.ApplicationConfig = ac
}
// Organizations returns a map of org ID to ApplicationOrg
func (ac *ApplicationConfig) Organizations() map[string]ApplicationOrg {
	return ac.applicationOrgs
}

/*** fabric/protos/peer/configuration.pb.go ***/
// AnchorPeers simply represents list of anchor peers which is used in ConfigurationItem
type AnchorPeersPROTOS struct { //WAS:AnchorPeers
	AnchorPeers []*AnchorPeerPROTOS `protobuf:"bytes,1,rep,name=anchor_peers,json=anchorPeers" json:"anchor_peers,omitempty"`
}
func (m *AnchorPeersPROTOS) Reset()                    { *m = AnchorPeersPROTOS{} } //WAS:AnchorPeers
func (m *AnchorPeersPROTOS) String() string            { return proto.CompactTextString(m) } //WAS:AnchorPeers
func (*AnchorPeersPROTOS) ProtoMessage()               {} //WAS:AnchorPeers
func (*AnchorPeersPROTOS) Descriptor() ([]byte, []int) { return fileDescriptor4PROTOS, []int{0} } //WAS:AnchorPeers //WAS:fileDescriptor4
func (m *AnchorPeersPROTOS) GetAnchorPeers() []*AnchorPeerPROTOS { //WAS:AnchorPeers
	if m != nil {
		return m.AnchorPeers
	}
	return nil
}
// AnchorPeer message structure which provides information about anchor peer, it includes host name,
// port number and peer certificate.
type AnchorPeerPROTOS struct { //WAS:AnchorPeer
	// DNS host name of the anchor peer
	Host string `protobuf:"bytes,1,opt,name=host" json:"host,omitempty"`
	// The port number
	Port int32 `protobuf:"varint,2,opt,name=port" json:"port,omitempty"`
}
func (m *AnchorPeerPROTOS) Reset()                    { *m = AnchorPeerPROTOS{} } //WAS:AnchorPeer
func (m *AnchorPeerPROTOS) String() string            { return proto.CompactTextString(m) } //WAS:AnchorPeer
func (*AnchorPeerPROTOS) ProtoMessage()               {} //WAS:AnchorPeer
func (*AnchorPeerPROTOS) Descriptor() ([]byte, []int) { return fileDescriptor4PROTOS, []int{1} } //WAS:AnchorPeer //WAS:fileDescriptor4
func (m *AnchorPeerPROTOS) GetHost() string { //WAS:AnchorPeer
	if m != nil {
		return m.Host
	}
	return ""
}
func (m *AnchorPeerPROTOS) GetPort() int32 { //WAS:AnchorPeer
	if m != nil {
		return m.Port
	}
	return 0
}
var fileDescriptor4PROTOS = []byte{ //WAS:fileDescriptor4
	// 192 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x09, 0x6e, 0x88, 0x02, 0xff, 0x4c, 0x8f, 0x3d, 0x8f, 0xc3, 0x20,
	0x0c, 0x86, 0xc5, 0x7d, 0x49, 0x47, 0x6e, 0x62, 0x62, 0x8c, 0x32, 0xe5, 0x16, 0x90, 0xee, 0xe3,
	0x07, 0xb4, 0xea, 0xde, 0x2a, 0x63, 0x97, 0x8a, 0x50, 0x02, 0x48, 0x6d, 0x8c, 0x0c, 0x19, 0xfa,
	0xef, 0x2b, 0x40, 0x55, 0x3a, 0xf1, 0x62, 0x3f, 0x8f, 0x6c, 0x53, 0x1e, 0x8c, 0x41, 0xa9, 0x61,
	0x9e, 0xbc, 0x5d, 0x50, 0x25, 0x0f, 0xb3, 0x08, 0x08, 0x09, 0xd8, 0x47, 0x79, 0x62, 0xb7, 0xa3,
	0xcd, 0x66, 0xd6, 0x0e, 0xf0, 0x60, 0x0c, 0x46, 0xf6, 0x4f, 0xbf, 0x54, 0xf9, 0x9e, 0xb2, 0x19,
	0x39, 0x69, 0x5f, 0xfb, 0xe6, 0x87, 0x55, 0x29, 0x8a, 0x15, 0x1d, 0x1a, 0xb5, 0x6a, 0xdd, 0x1f,
	0xa5, 0x6b, 0x8b, 0x31, 0xfa, 0xe6, 0x20, 0x26, 0x4e, 0x5a, 0xd2, 0x7f, 0x0e, 0x25, 0xe7, 0x5a,
	0x00, 0x4c, 0xfc, 0xa5, 0x25, 0xfd, 0xfb, 0x50, 0xf2, 0x76, 0x4f, 0x3b, 0x40, 0x2b, 0xdc, 0x2d,
	0x18, 0xbc, 0x98, 0xb3, 0x35, 0x28, 0x26, 0x35, 0xa2, 0xd7, 0x8f, 0x71, 0x79, 0x87, 0xe3, 0xb7,
	0xf5, 0xc9, 0x2d, 0xa3, 0xd0, 0x70, 0x95, 0x4f, 0xa8, 0xac, 0xa8, 0xac, 0xa8, 0xcc, 0xe8, 0x58,
	0x8f, 0xfa, 0xbd, 0x07, 0x00, 0x00, 0xff, 0xff, 0x6d, 0xf2, 0x7b, 0x6f, 0xf7, 0x00, 0x00, 0x00,
}

/*** fabric/common/config/applicationorg.go ***/
// AnchorPeersKey is the key name for the AnchorPeers ConfigValue
const AnchorPeersKey = "AnchorPeers"
type ApplicationOrgProtos struct {
	AnchorPeers *AnchorPeersPROTOS //WAS:AnchorPeers //SOURCE:pb.AnchorPeers
}
type ApplicationOrgConfig struct {
	*OrganizationConfig
	protos *ApplicationOrgProtos
	applicationOrgGroup *ApplicationOrgGroup
}
// ApplicationOrgGroup defines the configuration for an application org
type ApplicationOrgGroup struct {
	*ProposerCONFIG //WAS:Proposer
	*OrganizationGroup
	*ApplicationOrgConfig
}
// NewApplicationOrgGroup creates a new ApplicationOrgGroup
func NewApplicationOrgGroup(id string, mspConfig *MSPConfigHandler) *ApplicationOrgGroup { //SOURCE:mspconfig.MSPConfigHandler
	aog := &ApplicationOrgGroup{
		OrganizationGroup: NewOrganizationGroup(id, mspConfig),
	}
	aog.ProposerCONFIG = NewProposer(aog) //WAS:Proposer
	return aog
}
// AnchorPeers returns the list of valid orderer addresses to connect to to invoke Broadcast/Deliver
func (aog *ApplicationOrgConfig) AnchorPeers() []*AnchorPeerPROTOS { //WAS:AnchorPeer //SOURCE:pb.AnchorPeer
	return aog.protos.AnchorPeers.AnchorPeers
}
func (aog *ApplicationOrgGroup) Allocate() Values {
	return NewApplicationOrgConfig(aog)
}
func (aoc *ApplicationOrgConfig) Commit() {
	aoc.applicationOrgGroup.ApplicationOrgConfig = aoc
	aoc.OrganizationConfig.Commit()
}
func NewApplicationOrgConfig(aog *ApplicationOrgGroup) *ApplicationOrgConfig {
	aoc := &ApplicationOrgConfig{
		protos:             &ApplicationOrgProtos{},
		OrganizationConfig: NewOrganizationConfig(aog.OrganizationGroup),

		applicationOrgGroup: aog,
	}
	var err error
	aoc.standardValues, err = NewStandardValues(aoc.protos, aoc.OrganizationConfig.protos)
	if err != nil {
		logger.Panicf("Programming error: %s", err)
	}
	return aoc
}
func (aoc *ApplicationOrgConfig) Validate(tx interface{}, groups map[string]ValueProposer) error {
	if logger.IsEnabledFor(logging.DEBUG) {
		logger.Debugf("Anchor peers for org %s are %v", aoc.applicationOrgGroup.name, aoc.protos.AnchorPeers)
	}
	return aoc.OrganizationConfig.Validate(tx, groups)
}

/*** fabric/common/config/organization.go ***/
// MSPKey is value key for marshaled *mspconfig.MSPConfig
const MSPKey = "MSP"

/*** fabric/common/config/application_util.go ***/
func applicationConfigGroup(orgID string, key string, value []byte) *ConfigGroup { //SOURCE:cb.ConfigGroup
	result := NewConfigGroup() //SOURCE:cb.NewConfigGroup
	result.Groups[ApplicationGroupKey] = NewConfigGroup() //SOURCE:cb.NewConfigGroup
	result.Groups[ApplicationGroupKey].Groups[orgID] = NewConfigGroup() //SOURCE:cb.NewConfigGroup
	result.Groups[ApplicationGroupKey].Groups[orgID].Values[key] = &ConfigValue{ //SOURCE:cb.ConfigValue
		Value: value,
	}
	return result
}
// TemplateAnchorPeers creates a headerless config item representing the anchor peers
func TemplateAnchorPeers(orgID string, anchorPeers []*AnchorPeerPROTOS) *ConfigGroup { //SOURCE:cb.ConfigGroup //WAS:AnchorPeer //SOURCE:pb.AnchorPeer
	return applicationConfigGroup(orgID, AnchorPeersKey, MarshalOrPanic(&AnchorPeersPROTOS{AnchorPeers: anchorPeers})) //SOURCE:utils.MarshalOrPanic //WAS:AnchorPeers //SOURCE:pb.AnchorPeers
}

/*** fabric/common/config/consortiums.go ***/
const (
	// ChannelCreationPolicyKey is the key for the ChannelCreationPolicy value
	ChannelCreationPolicyKey = "ChannelCreationPolicy"
)
// TemplateConsortiumsGroup creates an empty consortiums group
func TemplateConsortiumsGroup() *ConfigGroup { //SOURCE:cb.ConfigGroup
	result := NewConfigGroup() //SOURCE:cb.NewConfigGroup
	result.Groups[ConsortiumsGroupKey] = NewConfigGroup() //SOURCE:cb.NewConfigGroup
	return result
}
// TemplateConsortiumChannelCreationPolicy sets the ChannelCreationPolicy for a given consortium
func TemplateConsortiumChannelCreationPolicy(name string, policy *Policy) *ConfigGroup { //SOURCE:cb.Policy //SOURCE:cb.ConfigGroup
	result := TemplateConsortiumsGroup()
	result.Groups[ConsortiumsGroupKey].Groups[name] = NewConfigGroup() //SOURCE:cb.NewConfigGroup
	result.Groups[ConsortiumsGroupKey].Groups[name].Values[ChannelCreationPolicyKey] = &ConfigValue{ //SOURCE:cb.ConfigValue
		Value: MarshalOrPanic(policy), //SOURCE:utils.MarshalOrPanic
	}
	return result
}

/*** fabric/common/config/consortium.go ***/
// ConsortiumProtos holds the config protos for the consortium config
type ConsortiumProtos struct {
	ChannelCreationPolicy *Policy //SOURCE:cb.Policy
}
// ConsortiumGroup stores the set of Consortium
type ConsortiumGroup struct {
	*ProposerCONFIG //WAS:Proposer
	*ConsortiumConfig
	mspConfig *MSPConfigHandler //SOURCE:msp.MSPConfigHandler
}
// NewConsortiumGroup creates a new *ConsortiumGroup
func NewConsortiumGroup(mspConfig *MSPConfigHandler) *ConsortiumGroup { //SOURCE:msp.MSPConfigHandler
	cg := &ConsortiumGroup{
		mspConfig: mspConfig,
	}
	cg.ProposerCONFIG = NewProposer(cg) //WAS:Proposer
	return cg
}
// NewGroup returns a Consortium instance
func (cg *ConsortiumGroup) NewGroup(name string) (ValueProposer, error) {
	return NewOrganizationGroup(name, cg.mspConfig), nil
}
// Allocate returns the resources for a new config proposal
func (cg *ConsortiumGroup) Allocate() Values {
	return NewConsortiumConfig(cg)
}
// BeginValueProposals calls through to Proposer after calling into the MSP config Handler
func (cg *ConsortiumGroup) BeginValueProposals(tx interface{}, groups []string) (ValueDeserializer, []ValueProposer, error) {
	return cg.ProposerCONFIG.BeginValueProposals(tx, groups) //WAS:Proposer
}
// PreCommit intercepts the precommit request and commits the MSP config handler before calling the underlying proposer
func (cg *ConsortiumGroup) PreCommit(tx interface{}) error {
	return cg.ProposerCONFIG.PreCommit(tx) //WAS:Proposer
}
// RollbackProposals intercepts the rollback request and commits the MSP config handler before calling the underlying proposer
func (cg *ConsortiumGroup) RollbackProposals(tx interface{}) {
	cg.ProposerCONFIG.RollbackProposals(tx) //WAS:Proposer
}
// CommitProposals intercepts the commit request and commits the MSP config handler before calling the underlying proposer
func (cg *ConsortiumGroup) CommitProposals(tx interface{}) {
	cg.ProposerCONFIG.CommitProposals(tx) //WAS:Proposer
}
// ConsortiumConfig holds the consoritums configuration information
type ConsortiumConfig struct {
	*standardValues
	protos *ConsortiumProtos
	orgs   map[string]*OrganizationGroup
	consortiumGroup *ConsortiumGroup
}
// NewConsortiumConfig creates a new instance of the consoritums config
func NewConsortiumConfig(cg *ConsortiumGroup) *ConsortiumConfig {
	cc := &ConsortiumConfig{
		protos:          &ConsortiumProtos{},
		orgs:            make(map[string]*OrganizationGroup),
		consortiumGroup: cg,
	}
	var err error
	cc.standardValues, err = NewStandardValues(cc.protos)
	if err != nil {
		logger.Panicf("Programming error: %s", err)
	}
	return cc
}
// Organizations returns the set of organizations in the consortium
func (cc *ConsortiumConfig) Organizations() map[string]*OrganizationGroup {
	return cc.orgs
}
// CreationPolicy returns the policy structure used to validate
// the channel creation
func (cc *ConsortiumConfig) ChannelCreationPolicy() *Policy { //SOURCE:cb.Policy
	return cc.protos.ChannelCreationPolicy
}
// Commit commits the ConsortiumConfig
func (cc *ConsortiumConfig) Commit() {
	cc.consortiumGroup.ConsortiumConfig = cc
}
// Validate builds the Consortium map
func (cc *ConsortiumConfig) Validate(tx interface{}, groups map[string]ValueProposer) error {
	var ok bool
	for key, group := range groups {
		cc.orgs[key], ok = group.(*OrganizationGroup)
		if !ok {
			return fmt.Errorf("Unexpected group type: %T", group)
		}
	}
	return nil
}

/*** fabric/common/config/consortiums.go ***/
const (
	// ConsortiumsGroupKey is the group name for the consortiums config
	ConsortiumsGroupKey = "Consortiums"
)
// ConsortiumsGroup stores the set of Consortiums
type ConsortiumsGroup struct {
	*ProposerCONFIG //WAS:Proposer
	*ConsortiumsConfig
	mspConfig *MSPConfigHandler //SOURCE:msp.MSPConfigHandler
}
// NewConsortiumsGroup creates a new *ConsortiumsGroup
func NewConsortiumsGroup(mspConfig *MSPConfigHandler) *ConsortiumsGroup { //SOURCE:msp.MSPConfigHandler
	cg := &ConsortiumsGroup{
		mspConfig: mspConfig,
	}
	cg.ProposerCONFIG = NewProposer(cg) //WAS:Proposer
	return cg
}
// NewGroup returns a Consortium instance
func (cg *ConsortiumsGroup) NewGroup(name string) (ValueProposer, error) {
	return NewConsortiumGroup(cg.mspConfig), nil
}
// Allocate returns the resources for a new config proposal
func (cg *ConsortiumsGroup) Allocate() Values {
	return NewConsortiumsConfig(cg)
}
// ConsortiumsConfig holds the consoritums configuration information
type ConsortiumsConfig struct {
	*standardValues
	consortiums map[string]ConsortiumCONFIG //WAS:Consortium
	consortiumsGroup *ConsortiumsGroup
}
// NewConsortiumsConfig creates a new instance of the consoritums config
func NewConsortiumsConfig(cg *ConsortiumsGroup) *ConsortiumsConfig {
	cc := &ConsortiumsConfig{
		consortiums:      make(map[string]ConsortiumCONFIG), //WAS:Consortium
		consortiumsGroup: cg,
	}
	var err error
	cc.standardValues, err = NewStandardValues()
	if err != nil {
		logger.Panicf("Programming error: %s", err)
	}
	return cc
}
// Consortiums returns a map of the current consortiums
func (cc *ConsortiumsConfig) Consortiums() map[string]ConsortiumCONFIG { //WAS:Consortium
	return cc.consortiums
}
// Commit commits the ConsortiumsConfig
func (cc *ConsortiumsConfig) Commit() {
	cc.consortiumsGroup.ConsortiumsConfig = cc
}
// Validate builds the Consortiums map
func (cc *ConsortiumsConfig) Validate(tx interface{}, groups map[string]ValueProposer) error {
	var ok bool
	for key, group := range groups {
		cc.consortiums[key], ok = group.(*ConsortiumGroup)
		if !ok {
			return fmt.Errorf("Unexpected group type: %T", group)
		}
	}
	return nil
}

/*** fabric/common/util/utils.go ***/
// ComputeSHA256 returns SHA2-256 on data
func ComputeSHA256(data []byte) (hash []byte) {
	hash, err := GetDefault().Hash(data, &SHA256Opts{}) //SOURCE:factory.GetDefault //SOURCE:bccsp.SHA256Opts
	if err != nil {
		panic(fmt.Errorf("Failed computing SHA256 on [% x]", data))
	}
	return
}
// ComputeSHA3256 returns SHA3-256 on data
func ComputeSHA3256(data []byte) (hash []byte) {
	hash, err := GetDefault().Hash(data, &SHA3_256Opts{}) //SOURCE:factory.GetDefault //SOURCE:bccsp.SHA3_256Opts
	if err != nil {
		panic(fmt.Errorf("Failed computing SHA3_256 on [% x]", data))
	}
	return
}
// ConcatenateBytes is useful for combining multiple arrays of bytes, especially for
// signatures or digests over multiple fields
func ConcatenateBytes(data ...[]byte) []byte {
	finalLength := 0
	for _, slice := range data {
		finalLength += len(slice)
	}
	result := make([]byte, finalLength)
	last := 0
	for _, slice := range data {
		for i := range slice {
			result[i+last] = slice[i]
		}
		last += len(slice)
	}
	return result
}

/*** fabric/common/configtx/template.go ***/
const (
	// CreationPolicyKey defines the config key used in the channel
	// config, under which the creation policy is defined.
	CreationPolicyKey = "CreationPolicy"
	msgVersion        = int32(0)
	epoch             = 0
)
// Template can be used to facilitate creation of config transactions
type Template interface {
	// Envelope returns a ConfigUpdateEnvelope for the given chainID
	Envelope(chainID string) (*ConfigUpdateEnvelope, error) //SOURCE:cb.ConfigUpdateEnvelope
}
type simpleTemplate struct {
	configGroup *ConfigGroup //SOURCE:cb.ConfigGroup
}
// NewSimpleTemplate creates a Template using the supplied ConfigGroups
func NewSimpleTemplate(configGroups ...*ConfigGroup) Template { //SOURCE:cb.ConfigGroup
	sts := make([]Template, len(configGroups))
	for i, group := range configGroups {
		sts[i] = &simpleTemplate{
			configGroup: group,
		}
	}
	return NewCompositeTemplate(sts...)
}
// Envelope returns a ConfigUpdateEnvelope for the given chainID
func (st *simpleTemplate) Envelope(chainID string) (*ConfigUpdateEnvelope, error) { //SOURCE:cb.ConfigUpdateEnvelope
	config, err := proto.Marshal(&ConfigUpdate{ //SOURCE:cb.ConfigUpdate
		ChannelId: chainID,
		WriteSet:  st.configGroup,
	})
	if err != nil {
		return nil, err
	}
	return &ConfigUpdateEnvelope{ //SOURCE:cb.ConfigUpdateEnvelope
		ConfigUpdate: config,
	}, nil
}
type compositeTemplate struct {
	templates []Template
}
// NewCompositeTemplate creates a Template using the source Templates
func NewCompositeTemplate(templates ...Template) Template {
	return &compositeTemplate{templates: templates}
}
func copyGroup(source *ConfigGroup, target *ConfigGroup) error { //SOURCE:cb.ConfigGroup
	for key, value := range source.Values {
		_, ok := target.Values[key]
		if ok {
			return fmt.Errorf("Duplicate key: %s", key)
		}
		target.Values[key] = value
	}
	for key, policy := range source.Policies {
		_, ok := target.Policies[key]
		if ok {
			return fmt.Errorf("Duplicate policy: %s", key)
		}
		target.Policies[key] = policy
	}
	for key, group := range source.Groups {
		_, ok := target.Groups[key]
		if !ok {
			newGroup := NewConfigGroup() //SOURCE:cb.NewConfigGroup
			newGroup.ModPolicy = group.ModPolicy
			target.Groups[key] = newGroup
		}
		err := copyGroup(group, target.Groups[key])
		if err != nil {
			return fmt.Errorf("Error copying group %s: %s", key, err)
		}
	}
	return nil
}
// Envelope returns a ConfigUpdateEnvelope for the given chainID
func (ct *compositeTemplate) Envelope(chainID string) (*ConfigUpdateEnvelope, error) { //SOURCE:cb.ConfigUpdateEnvelope
	channel := NewConfigGroup() //SOURCE:cb.NewConfigGroup
	for i := range ct.templates {
		configEnv, err := ct.templates[i].Envelope(chainID)
		if err != nil {
			return nil, err
		}
		config, err := UnmarshalConfigUpdate(configEnv.ConfigUpdate)
		if err != nil {
			return nil, err
		}
		err = copyGroup(config.WriteSet, channel)
		if err != nil {
			return nil, err
		}
	}
	marshaledConfig, err := proto.Marshal(&ConfigUpdate{ //SOURCE:cb.ConfigUpdate
		ChannelId: chainID,
		WriteSet:  channel,
	})
	if err != nil {
		return nil, err
	}
	return &ConfigUpdateEnvelope{ConfigUpdate: marshaledConfig}, nil //SOURCE:cb.ConfigUpdateEnvelope
}
type modPolicySettingTemplate struct {
	modPolicy string
	template  Template
}
// NewModPolicySettingTemplate wraps another template and sets the ModPolicy of
// every ConfigGroup/ConfigValue/ConfigPolicy without a modPolicy to modPolicy
func NewModPolicySettingTemplate(modPolicy string, template Template) Template {
	return &modPolicySettingTemplate{
		modPolicy: modPolicy,
		template:  template,
	}
}
func setGroupModPolicies(modPolicy string, group *ConfigGroup) { //SOURCE:cb.ConfigGroup
	if group.ModPolicy == "" {
		group.ModPolicy = modPolicy
	}
	for _, value := range group.Values {
		if value.ModPolicy != "" {
			continue
		}
		value.ModPolicy = modPolicy
	}
	for _, policy := range group.Policies {
		if policy.ModPolicy != "" {
			continue
		}
		policy.ModPolicy = modPolicy
	}
	for _, nextGroup := range group.Groups {
		setGroupModPolicies(modPolicy, nextGroup)
	}
}
func (mpst *modPolicySettingTemplate) Envelope(channelID string) (*ConfigUpdateEnvelope, error) { //SOURCE:cb.ConfigUpdateEnvelope
	configUpdateEnv, err := mpst.template.Envelope(channelID)
	if err != nil {
		return nil, err
	}
	config, err := UnmarshalConfigUpdate(configUpdateEnv.ConfigUpdate)
	if err != nil {
		return nil, err
	}
	setGroupModPolicies(mpst.modPolicy, config.WriteSet)
	configUpdateEnv.ConfigUpdate = MarshalOrPanic(config) //SOURCE:utils.MarshalOrPanic
	return configUpdateEnv, nil
}
type channelCreationTemplate struct {
	consortiumName string
	orgs           []string
}
// NewChainCreationTemplate takes a consortium name and a Template to produce a
// Template which outputs an appropriately constructed list of ConfigUpdateEnvelopes.
func NewChainCreationTemplate(consortiumName string, orgs []string) Template {
	return &channelCreationTemplate{
		consortiumName: consortiumName,
		orgs:           orgs,
	}
}
func (cct *channelCreationTemplate) Envelope(channelID string) (*ConfigUpdateEnvelope, error) { //SOURCE:cb.ConfigUpdateEnvelope
	rSet := TemplateConsortium(cct.consortiumName) //SOURCE:config.TemplateConsortium
	wSet := TemplateConsortium(cct.consortiumName) //SOURCE:config.TemplateConsortium
	rSet.Groups[ApplicationGroupKey] = NewConfigGroup() //SOURCE:config.ApplicationGroupKey //SOURCE:cb.NewConfigGroup
	wSet.Groups[ApplicationGroupKey] = NewConfigGroup() //SOURCE:config.ApplicationGroupKey //SOURCE:cb.NewConfigGroup
	for _, org := range cct.orgs {
		rSet.Groups[ApplicationGroupKey].Groups[org] = NewConfigGroup() //SOURCE:config.ApplicationGroupKey //SOURCE:cb.NewConfigGroup
		wSet.Groups[ApplicationGroupKey].Groups[org] = NewConfigGroup() //SOURCE:config.ApplicationGroupKey //SOURCE:cb.NewConfigGroup
	}
	wSet.Groups[ApplicationGroupKey].ModPolicy = AdminsPolicyKey //SOURCE:config.ApplicationGroupKey //SOURCE:configmsp.AdminsPolicyKey
	wSet.Groups[ApplicationGroupKey].Policies[AdminsPolicyKey] = ImplicitMetaPolicyWithSubPolicy(AdminsPolicyKey, ImplicitMetaPolicy_MAJORITY) //SOURCE:config.ApplicationGroupKey //SOURCE:configmsp.AdminsPolicyKey //SOURCE:policies.ImplicitMetaPolicyWithSubPolicy //SOURCE:cb.ImplicitMetaPolicy_MAJORITY
	wSet.Groups[ApplicationGroupKey].Policies[AdminsPolicyKey].ModPolicy = AdminsPolicyKey //SOURCE:config.ApplicationGroupKey //SOURCE:configmsp.AdminsPolicyKey
	wSet.Groups[ApplicationGroupKey].Policies[WritersPolicyKey] = ImplicitMetaPolicyWithSubPolicy(WritersPolicyKey, ImplicitMetaPolicy_ANY) //SOURCE:config.ApplicationGroupKey //SOURCE:configmsp.WritersPolicyKey //SOURCE:policies.ImplicitMetaPolicyWithSubPolicy //SOURCE:cb.ImplicitMetaPolicy_ANY
	wSet.Groups[ApplicationGroupKey].Policies[WritersPolicyKey].ModPolicy = AdminsPolicyKey //SOURCE:config.ApplicationGroupKey //SOURCE:configmsp.WritersPolicyKey
	wSet.Groups[ApplicationGroupKey].Policies[ReadersPolicyKey] = ImplicitMetaPolicyWithSubPolicy(ReadersPolicyKey, ImplicitMetaPolicy_ANY) //SOURCE:config.ApplicationGroupKey //SOURCE:configmsp.ReadersPolicyKey //SOURCE:policies.ImplicitMetaPolicyWithSubPolicy //SOURCE:cb.ImplicitMetaPolicy_ANY
	wSet.Groups[ApplicationGroupKey].Policies[ReadersPolicyKey].ModPolicy = AdminsPolicyKey //SOURCE:config.ApplicationGroupKey //SOURCE:configmsp.ReadersPolicyKey
	wSet.Groups[ApplicationGroupKey].Version = 1 //SOURCE:config.ApplicationGroupKey
	return &ConfigUpdateEnvelope{ //SOURCE:cb.ConfigUpdateEnvelope
		ConfigUpdate: MarshalOrPanic(&ConfigUpdate{ //SOURCE:utils.MarshalOrPanic //SOURCE:cb.ConfigUpdate
			ChannelId: channelID,
			ReadSet:   rSet,
			WriteSet:  wSet,
		}),
	}, nil
}
// MakeChainCreationTransaction is a handy utility function for creating new chain transactions using the underlying Template framework
func MakeChainCreationTransaction(channelID string, consortium string, signer SigningIdentity, orgs ...string) (*Envelope, error) { //SOURCE:msp.SigningIdentity //SOURCE:cb.Envelope
	newChainTemplate := NewChainCreationTemplate(consortium, orgs)
	newConfigUpdateEnv, err := newChainTemplate.Envelope(channelID)
	if err != nil {
		return nil, err
	}
	payloadSignatureHeader := &SignatureHeader{} //SOURCE:cb.SignatureHeader
	if signer != nil {
		sSigner, err := signer.Serialize()
		if err != nil {
			return nil, fmt.Errorf("Serialization of identity failed, err %s", err)
		}
		newConfigUpdateEnv.Signatures = []*ConfigSignature{&ConfigSignature{ //SOURCE:cb.ConfigSignature
			SignatureHeader: MarshalOrPanic(MakeSignatureHeader(sSigner, CreateNonceOrPanic())), //SOURCE:utils.MarshalOrPanic //SOURCE:utils.MakeSignatureHeader //SOURCE:utils.CreateNonceOrPanic
		}}
		newConfigUpdateEnv.Signatures[0].Signature, err = signer.Sign(ConcatenateBytes(newConfigUpdateEnv.Signatures[0].SignatureHeader, newConfigUpdateEnv.ConfigUpdate)) //SOURCE:util.ConcatenateBytes
		if err != nil {
			return nil, err
		}
		payloadSignatureHeader = MakeSignatureHeader(sSigner, CreateNonceOrPanic()) //SOURCE:utils.MakeSignatureHeader //SOURCE:utils.CreateNonceOrPanic
	}
	payloadChannelHeader := MakeChannelHeader(HeaderType_CONFIG_UPDATE, msgVersion, channelID, epoch) //SOURCE:utils.MakeChannelHeader //SOURCE:cb.HeaderType_CONFIG_UPDATE
	SetTxID(payloadChannelHeader, payloadSignatureHeader) //SOURCE:utils.SetTxID
	payloadHeader := MakePayloadHeader(payloadChannelHeader, payloadSignatureHeader) //SOURCE:utils.MakePayloadHeader
	payload := &Payload{Header: payloadHeader, Data: MarshalOrPanic(newConfigUpdateEnv)} //SOURCE:cb.Payload //SOURCE:utils.MarshalOrPanic
	paylBytes := MarshalOrPanic(payload) //SOURCE:utils.MarshalOrPanic
	var sig []byte
	if signer != nil {
		// sign the payload
		sig, err = signer.Sign(paylBytes)
		if err != nil {
			return nil, err
		}
	}
	return &Envelope{Payload: paylBytes, Signature: sig}, nil //SOURCE:cb.Envelope
}

/*** fabric/common/config/proposer.go ***/
// ValueDeserializer provides a mechanism to retrieve proto messages to deserialize config values into
type ValueDeserializer interface {
	// Deserialize takes a Value key as a string, and a marshaled Value value as bytes
	// and returns the deserialized version of that value.  Note, this function operates
	// with side effects intended.  Using a ValueDeserializer to deserialize a message will
	// generally set the value in the Values interface that the ValueDeserializer derived from
	// Therefore, the proto.Message may be safely discarded, but may be retained for
	// inspection and or debugging purposes.
	Deserialize(key string, value []byte) (proto.Message, error)
}
// Values defines a mechanism to supply messages to unamrshal from config
// and a mechanism to validate the results
type Values interface {
	ValueDeserializer
	// Validate should ensure that the values set into the proto messages are correct
	// and that the new group values are allowed.  It also includes a tx ID in case cross
	// Handler invocations (ie to the MSP Config Manager) must be made
	Validate(interface{}, map[string]ValueProposer) error
	// Commit should call back into the Value handler to update the config
	Commit()
}
// Handler
type Handler interface {
	Allocate() Values
	NewGroup(name string) (ValueProposer, error)
}
type configCONFIG struct { //WAS:config
	allocated Values
	groups    map[string]ValueProposer
}
type ProposerCONFIG struct { //WAS:Proposer
	vh          Handler
	pending     map[interface{}]*configCONFIG //WAS:config
	current     *configCONFIG //WAS:config
	pendingLock sync.RWMutex
}
func NewProposer(vh Handler) *ProposerCONFIG { //WAS:Proposer
	return &ProposerCONFIG{ //WAS:Proposer
		vh:      vh,
		current: &configCONFIG{}, //WAS:config
		pending: make(map[interface{}]*configCONFIG), //WAS:config
	}
}
// BeginValueProposals called when a config proposal is begun
func (p *ProposerCONFIG) BeginValueProposals(tx interface{}, groups []string) (ValueDeserializer, []ValueProposer, error) { //WAS:Proposer
	p.pendingLock.Lock()
	defer p.pendingLock.Unlock()
	if _, ok := p.pending[tx]; ok {
		logger.Panicf("Duplicated BeginValueProposals without Rollback or Commit")
	}
	result := make([]ValueProposer, len(groups))
	pending := &configCONFIG{ //WAS:config
		allocated: p.vh.Allocate(),
		groups:    make(map[string]ValueProposer),
	}
	for i, groupName := range groups {
		var group ValueProposer
		var ok bool
		if p.current == nil {
			ok = false
		} else {
			group, ok = p.current.groups[groupName]
		}
		if !ok {
			var err error
			group, err = p.vh.NewGroup(groupName)
			if err != nil {
				pending = nil
				return nil, nil, fmt.Errorf("Error creating group %s: %s", groupName, err)
			}
		}
		pending.groups[groupName] = group
		result[i] = group
	}
	p.pending[tx] = pending
	return pending.allocated, result, nil
}
// Validate ensures that the new config values is a valid change
func (p *ProposerCONFIG) PreCommit(tx interface{}) error { //WAS:Proposer
	p.pendingLock.RLock()
	pending, ok := p.pending[tx]
	p.pendingLock.RUnlock()
	if !ok {
		logger.Panicf("Serious Programming Error: attempted to pre-commit tx which had not been begun")
	}
	return pending.allocated.Validate(tx, pending.groups)
}
// RollbackProposals called when a config proposal is abandoned
func (p *ProposerCONFIG) RollbackProposals(tx interface{}) { //WAS:Proposer
	p.pendingLock.Lock()
	defer p.pendingLock.Unlock()
	delete(p.pending, tx)
}
// CommitProposals called when a config proposal is committed
func (p *ProposerCONFIG) CommitProposals(tx interface{}) { //WAS:Proposer
	p.pendingLock.Lock()
	defer p.pendingLock.Unlock()
	pending, ok := p.pending[tx]
	if !ok {
		logger.Panicf("Serious Programming Error: attempted to commit tx which had not been begun")
	}
	p.current = pending
	p.current.allocated.Commit()
	delete(p.pending, tx)
}

/*** fabric/common/config/api.go ***/
// Org stores the common organizational config
type Org interface {
	// Name returns the name this org is referred to in config
	Name() string
	// MSPID returns the MSP ID associated with this org
	MSPID() string
}
// ApplicationOrg stores the per org application config
type ApplicationOrg interface {
	Org
	// AnchorPeers returns the list of gossip anchor peers
	AnchorPeers() []*AnchorPeerPROTOS //WAS:AnchorPeer //SOURCE:pb.AnchorPeer
}
// Application stores the common shared application config
type ApplicationCOMMONCONFIG interface {
	// Organizations returns a map of org ID to ApplicationOrg
	Organizations() map[string]ApplicationOrg
}
// Channel gives read only access to the channel configuration
type Channel interface {
	// HashingAlgorithm returns the default algorithm to be used when hashing
	// such as computing block hashes, and CreationPolicy digests
	HashingAlgorithm() func(input []byte) []byte
	// BlockDataHashingStructureWidth returns the width to use when constructing the
	// Merkle tree to compute the BlockData hash
	BlockDataHashingStructureWidth() uint32
	// OrdererAddresses returns the list of valid orderer addresses to connect to to invoke Broadcast/Deliver
	OrdererAddresses() []string
}
// Consortiums represents the set of consortiums serviced by an ordering service
type ConsortiumsCOMMONCONFIG interface { //WAS:Consortiums
	// Consortiums returns the set of consortiums
	Consortiums() map[string]ConsortiumCONFIG //WAS:Consortium
}
// Consortium represents a group of orgs which may create channels together
type ConsortiumCONFIG interface { //WAS:Consortium
	// ChannelCreationPolicy returns the policy to check when instantiating a channel for this consortium
	ChannelCreationPolicy() *Policy //SOURCE:cb.Policy
}
// Orderer stores the common shared orderer config
type OrdererCOMMONCONFIG interface { //WAS:Orderer
	// ConsensusType returns the configured consensus type
	ConsensusType() string
	// BatchSize returns the maximum number of messages to include in a block
	BatchSize() *BatchSizeORDERER //WAS:BatchSize //SOURCE:ab.BatchSize
	// BatchTimeout returns the amount of time to wait before creating a batch
	BatchTimeout() time.Duration
	// MaxChannelsCount returns the maximum count of channels to allow for an ordering network
	MaxChannelsCount() uint64
	// KafkaBrokers returns the addresses (IP:port notation) of a set of "bootstrap"
	// Kafka brokers, i.e. this is not necessarily the entire set of Kafka brokers
	// used for ordering
	KafkaBrokers() []string
	// Organizations returns the organizations for the ordering service
	Organizations() map[string]Org
}
type ValueProposer interface {
	// BeginValueProposals called when a config proposal is begun
	BeginValueProposals(tx interface{}, groups []string) (ValueDeserializer, []ValueProposer, error)
	// RollbackProposals called when a config proposal is abandoned
	RollbackProposals(tx interface{})
	// PreCommit is invoked before committing the config to catch
	// any errors which cannot be caught on a per proposal basis
	// TODO, rename other methods to remove Value/Proposal references
	PreCommit(tx interface{}) error
	// CommitProposals called when a config proposal is committed
	CommitProposals(tx interface{})
}

/*** fabric/common/configtx/api/api.go ***/
// Manager provides a mechanism to query and update config
type Manager interface {
	Resources
	// Apply attempts to apply a configtx to become the new config
	Apply(configEnv *ConfigEnvelope) error //SOURCE:cb.ConfigEnvelope
	// Validate attempts to apply a configtx to become the new config
	Validate(configEnv *ConfigEnvelope) error //SOURCE:cb.ConfigEnvelope
	// Validate attempts to validate a new configtx against the current config state
	ProposeConfigUpdate(configtx *Envelope) (*ConfigEnvelope, error) //SOURCE:cb.Envelope //SOURCE:cb.ConfigEnvelope
	// ChainID retrieves the chain ID associated with this manager
	ChainID() string
	// ConfigEnvelope returns the current config envelope
	ConfigEnvelope() *ConfigEnvelope //SOURCE:cb.ConfigEnvelope
	// Sequence returns the current sequence number of the config
	Sequence() uint64
}
// Resources is the common set of config resources for all channels
// Depending on whether chain is used at the orderer or at the peer, other
// config resources may be available
type Resources interface {
	// PolicyManager returns the policies.Manager for the channel
	PolicyManager() ManagerPOLICIES //WAS:Manager //SOURCE:policies.Manager
	// ChannelConfig returns the config.Channel for the chain
	ChannelConfig() Channel //SOURCE:config.Channel
	// OrdererConfig returns the config.Orderer for the channel
	// and whether the Orderer config exists
	OrdererConfig() (OrdererCOMMONCONFIG, bool) //WAS:Orderer //SOURCE:config.Orderer
	// ConsortiumsConfig() returns the config.Consortiums for the channel
	// and whether the consortiums config exists
	ConsortiumsConfig() (ConsortiumsCOMMONCONFIG, bool) //WAS:Consortiums //SOURCE:config.Consortiums
	// ApplicationConfig returns the configtxapplication.SharedConfig for the channel
	// and whether the Application config exists
	ApplicationConfig() (ApplicationCOMMONCONFIG, bool) //WAS:Application //SOURCE:config.Application
	// MSPManager returns the msp.MSPManager for the chain
	MSPManager() MSPManager //SOURCE:msp.MSPManager
}
// Transactional is an interface which allows for an update to be proposed and rolled back
type Transactional interface {
	// RollbackConfig called when a config proposal is abandoned
	RollbackProposals(tx interface{})
	// PreCommit verifies that the transaction can be committed successfully
	PreCommit(tx interface{}) error
	// CommitConfig called when a config proposal is committed
	CommitProposals(tx interface{})
}
// PolicyHandler is used for config updates to policy
type PolicyHandler interface {
	Transactional
	BeginConfig(tx interface{}, groups []string) ([]PolicyHandler, error)
	ProposePolicy(tx interface{}, key string, path []string, policy *ConfigPolicy) (proto.Message, error) //SOURCE:cb.ConfigPolicy
}
// Proposer contains the references necesssary to appropriately unmarshal
// a cb.ConfigGroup
type Proposer interface {
	// ValueProposer return the root value proposer
	ValueProposer() ValueProposer //SOURCE:config.ValueProposer
	// PolicyProposer return the root policy proposer
	PolicyProposer() ProposerPOLICIES //WAS:Proposer //SOURCE:policies.Proposer
}
// Initializer is used as indirection between Manager and Handler to allow
// for single Handlers to handle multiple paths
type Initializer interface {
	Proposer
	Resources
}

/*** fabric/common/configtx/manager.go ***/
// Constraints for valid channel and config IDs
var (
	channelAllowedChars = "[a-z][a-z0-9.-]*"
	configAllowedChars  = "[a-zA-Z0-9.-]+"
	maxLength           = 249
	illegalNames        = map[string]struct{}{
		".":  struct{}{},
		"..": struct{}{},
	}
)
type configSet struct {
	channelID string
	sequence  uint64
	configMap map[string]comparable
	configEnv *ConfigEnvelope //SOURCE:cb.ConfigEnvelope
}
type configManager struct {
	Resources //SOURCE:api.Resources
	callOnUpdate []func(Manager) //SOURCE:api.Manager
	initializer  Initializer //SOURCE:api.Initializer
	current      *configSet
}
// validateConfigID makes sure that the config element names (ie map key of
// ConfigGroup) comply with the following restrictions
//      1. Contain only ASCII alphanumerics, dots '.', dashes '-'
//      2. Are shorter than 250 characters.
//      3. Are not the strings "." or "..".
func validateConfigID(configID string) error {
	re, _ := regexp.Compile(configAllowedChars)
	// Length
	if len(configID) <= 0 {
		return fmt.Errorf("config ID illegal, cannot be empty")
	}
	if len(configID) > maxLength {
		return fmt.Errorf("config ID illegal, cannot be longer than %d", maxLength)
	}
	// Illegal name
	if _, ok := illegalNames[configID]; ok {
		return fmt.Errorf("name '%s' for config ID is not allowed", configID)
	}
	// Illegal characters
	matched := re.FindString(configID)
	if len(matched) != len(configID) {
		return fmt.Errorf("config ID '%s' contains illegal characters", configID)
	}
	return nil
}

/*** fabric/common/configtx/configmap.go ***/
const (
	RootGroupKey = "Channel"
	GroupPrefix  = "[Groups] "
	ValuePrefix  = "[Values] "
	PolicyPrefix = "[Policy] " // The plurarility doesn't match, but, it makes the logs much easier being the same length as "Groups" and "Values"
	PathSeparator = "/"
)
// MapConfig is intended to be called outside this file
// it takes a ConfigGroup and generates a map of fqPath to comparables (or error on invalid keys)
func MapConfig(channelGroup *ConfigGroup) (map[string]comparable, error) { //SOURCE:cb.ConfigGroup
	result := make(map[string]comparable)
	if channelGroup != nil {
		err := recurseConfig(result, []string{RootGroupKey}, channelGroup)
		if err != nil {
			return nil, err
		}
	}
	return result, nil
}
// addToMap is used only internally by MapConfig
func addToMap(cg comparable, result map[string]comparable) error {
	var fqPath string
	switch {
	case cg.ConfigGroup != nil:
		fqPath = GroupPrefix
	case cg.ConfigValue != nil:
		fqPath = ValuePrefix
	case cg.ConfigPolicy != nil:
		fqPath = PolicyPrefix
	}
	if err := validateConfigID(cg.key); err != nil {
		return fmt.Errorf("Illegal characters in key: %s", fqPath)
	}
	if len(cg.path) == 0 {
		fqPath += PathSeparator + cg.key
	} else {
		fqPath += PathSeparator + strings.Join(cg.path, PathSeparator) + PathSeparator + cg.key
	}
	logger.Debugf("Adding to config map: %s", fqPath)
	result[fqPath] = cg
	return nil
}
// recurseConfig is used only internally by MapConfig
func recurseConfig(result map[string]comparable, path []string, group *ConfigGroup) error { //SOURCE:cb.ConfigGroup
	if err := addToMap(comparable{key: path[len(path)-1], path: path[:len(path)-1], ConfigGroup: group}, result); err != nil {
		return err
	}
	for key, group := range group.Groups {
		nextPath := make([]string, len(path)+1)
		copy(nextPath, path)
		nextPath[len(nextPath)-1] = key
		if err := recurseConfig(result, nextPath, group); err != nil {
			return err
		}
	}
	for key, value := range group.Values {
		if err := addToMap(comparable{key: key, path: path, ConfigValue: value}, result); err != nil {
			return err
		}
	}
	for key, policy := range group.Policies {
		if err := addToMap(comparable{key: key, path: path, ConfigPolicy: policy}, result); err != nil {
			return err
		}
	}
	return nil
}

/*** fabric/common/configtx/compare.go ***/
type comparable struct {
	*ConfigGroup //SOURCE:cb.ConfigGroup
	*ConfigValue //SOURCE:cb.ConfigValue
	*ConfigPolicy //SOURCE:cb.ConfigPolicy
	key  string
	path []string
}
func (cg comparable) equals(other comparable) bool {
	switch {
	case cg.ConfigGroup != nil:
		if other.ConfigGroup == nil {
			return false
		}
		return equalConfigGroup(cg.ConfigGroup, other.ConfigGroup)
	case cg.ConfigValue != nil:
		if other.ConfigValue == nil {
			return false
		}
		return equalConfigValues(cg.ConfigValue, other.ConfigValue)
	case cg.ConfigPolicy != nil:
		if other.ConfigPolicy == nil {
			return false
		}
		return equalConfigPolicies(cg.ConfigPolicy, other.ConfigPolicy)
	}
	// Unreachable
	return false
}
func (cg comparable) version() uint64 {
	switch {
	case cg.ConfigGroup != nil:
		return cg.ConfigGroup.Version
	case cg.ConfigValue != nil:
		return cg.ConfigValue.Version
	case cg.ConfigPolicy != nil:
		return cg.ConfigPolicy.Version
	}
	// Unreachable
	return 0
}
func (cg comparable) modPolicy() string {
	switch {
	case cg.ConfigGroup != nil:
		return cg.ConfigGroup.ModPolicy
	case cg.ConfigValue != nil:
		return cg.ConfigValue.ModPolicy
	case cg.ConfigPolicy != nil:
		return cg.ConfigPolicy.ModPolicy
	}
	// Unreachable
	return ""
}
func equalConfigValues(lhs, rhs *ConfigValue) bool { //SOURCE:cb.ConfigValue
	return lhs.Version == rhs.Version &&
		lhs.ModPolicy == rhs.ModPolicy &&
		bytes.Equal(lhs.Value, rhs.Value)
}
func equalConfigPolicies(lhs, rhs *ConfigPolicy) bool { //SOURCE:cb.ConfigPolicy
	if lhs.Version != rhs.Version ||
		lhs.ModPolicy != rhs.ModPolicy {
		return false
	}
	if lhs.Policy == nil || rhs.Policy == nil {
		return lhs.Policy == rhs.Policy
	}
	return lhs.Policy.Type == rhs.Policy.Type &&
		bytes.Equal(lhs.Policy.Value, rhs.Policy.Value)
}
// The subset functions check if inner is a subset of outer
// TODO, try to consolidate these three methods into one, as the code
// contents are the same, but the function signatures need to be different
func subsetOfGroups(inner, outer map[string]*ConfigGroup) bool { //SOURCE:cb.ConfigGroup
	// The empty set is a subset of all sets
	if len(inner) == 0 {
		return true
	}
	// If inner has more elements than outer, it cannot be a subset
	if len(inner) > len(outer) {
		return false
	}
	// If any element in inner is not in outer, it is not a subset
	for key := range inner {
		if _, ok := outer[key]; !ok {
			return false
		}
	}
	return true
}
func subsetOfPolicies(inner, outer map[string]*ConfigPolicy) bool { //SOURCE:cb.ConfigPolicy
	// The empty set is a subset of all sets
	if len(inner) == 0 {
		return true
	}
	// If inner has more elements than outer, it cannot be a subset
	if len(inner) > len(outer) {
		return false
	}
	// If any element in inner is not in outer, it is not a subset
	for key := range inner {
		if _, ok := outer[key]; !ok {
			return false
		}
	}
	return true
}
func subsetOfValues(inner, outer map[string]*ConfigValue) bool { //SOURCE:cb.ConfigValue
	// The empty set is a subset of all sets
	if len(inner) == 0 {
		return true
	}
	// If inner has more elements than outer, it cannot be a subset
	if len(inner) > len(outer) {
		return false
	}
	// If any element in inner is not in outer, it is not a subset
	for key := range inner {
		if _, ok := outer[key]; !ok {
			return false
		}
	}
	return true
}
func equalConfigGroup(lhs, rhs *ConfigGroup) bool { //SOURCE:cb.ConfigGroup
	if lhs.Version != rhs.Version ||
		lhs.ModPolicy != rhs.ModPolicy {
		return false
	}
	if !subsetOfGroups(lhs.Groups, rhs.Groups) ||
		!subsetOfGroups(rhs.Groups, lhs.Groups) ||
		!subsetOfPolicies(lhs.Policies, rhs.Policies) ||
		!subsetOfPolicies(rhs.Policies, lhs.Policies) ||
		!subsetOfValues(lhs.Values, rhs.Values) ||
		!subsetOfValues(rhs.Values, lhs.Values) {
		return false
	}
	return true
}

/*** fabric/common/configtx/update.go ***/
func ComputeDeltaSet(readSet, writeSet map[string]comparable) map[string]comparable {
	result := make(map[string]comparable)
	for key, value := range writeSet {
		readVal, ok := readSet[key]
		if ok && readVal.version() == value.version() {
			continue
		}
		// If the key in the readset is a different version, we include it
		// Error checking on the sanity of the update is done against the current config
		result[key] = value
	}
	return result
}

/*** fabric/common/configtx/util.go ***/
// UnmarshalConfig attempts to unmarshal bytes to a *cb.Config
func UnmarshalConfig(data []byte) (*Config, error) { //SOURCE:cb.Config
	config := &Config{} //SOURCE:cb.Config
	err := proto.Unmarshal(data, config)
	if err != nil {
		return nil, err
	}
	return config, nil
}
// UnmarshalConfig attempts to unmarshal bytes to a *cb.Config
func UnmarshalConfigOrPanic(data []byte) *Config { //SOURCE:cb.Config
	result, err := UnmarshalConfig(data)
	if err != nil {
		panic(err)
	}
	return result
}
// UnmarshalConfigUpdate attempts to unmarshal bytes to a *cb.ConfigUpdate
func UnmarshalConfigUpdate(data []byte) (*ConfigUpdate, error) { //SOURCE:cb.ConfigUpdate
	configUpdate := &ConfigUpdate{} //SOURCE:cb.ConfigUpdate
	err := proto.Unmarshal(data, configUpdate)
	if err != nil {
		return nil, err
	}
	return configUpdate, nil
}
// UnmarshalConfigUpdate attempts to unmarshal bytes to a *cb.ConfigUpdate or panics
func UnmarshalConfigUpdateOrPanic(data []byte) *ConfigUpdate { //SOURCE:cb.ConfigUpdate
	result, err := UnmarshalConfigUpdate(data)
	if err != nil {
		panic(err)
	}
	return result
}
// UnmarshalConfigUpdateEnvelope attempts to unmarshal bytes to a *cb.ConfigUpdate
func UnmarshalConfigUpdateEnvelope(data []byte) (*ConfigUpdateEnvelope, error) { //SOURCE:cb.ConfigUpdateEnvelope
	configUpdateEnvelope := &ConfigUpdateEnvelope{} //SOURCE:cb.ConfigUpdateEnvelope
	err := proto.Unmarshal(data, configUpdateEnvelope)
	if err != nil {
		return nil, err
	}
	return configUpdateEnvelope, nil
}
// UnmarshalConfigUpdateEnvelope attempts to unmarshal bytes to a *cb.ConfigUpdateEnvelope or panics
func UnmarshalConfigUpdateEnvelopeOrPanic(data []byte) *ConfigUpdateEnvelope { //SOURCE:cb.ConfigUpdateEnvelope
	result, err := UnmarshalConfigUpdateEnvelope(data)
	if err != nil {
		panic(err)
	}
	return result
}
// UnmarshalConfigEnvelope attempts to unmarshal bytes to a *cb.ConfigEnvelope
func UnmarshalConfigEnvelope(data []byte) (*ConfigEnvelope, error) { //SOURCE:cb.ConfigEnvelope
	configEnv := &ConfigEnvelope{} //SOURCE:cb.ConfigEnvelope
	err := proto.Unmarshal(data, configEnv)
	if err != nil {
		return nil, err
	}
	return configEnv, nil
}
// UnmarshalConfigEnvelope attempts to unmarshal bytes to a *cb.ConfigEnvelope or panics
func UnmarshalConfigEnvelopeOrPanic(data []byte) *ConfigEnvelope { //SOURCE:cb.ConfigEnvelope
	result, err := UnmarshalConfigEnvelope(data)
	if err != nil {
		panic(err)
	}
	return result
}

/*** fabric/protos/common/block.go ***/
// NewBlock construct a block with no data and no metadata.
func NewBlock(seqNum uint64, previousHash []byte) *Block {
	block := &Block{}
	block.Header = &BlockHeader{}
	block.Header.Number = seqNum
	block.Header.PreviousHash = previousHash
	block.Data = &BlockData{}
	var metadataContents [][]byte
	for i := 0; i < len(BlockMetadataIndex_name); i++ {
		metadataContents = append(metadataContents, []byte{})
	}
	block.Metadata = &BlockMetadata{Metadata: metadataContents}
	return block
}
type asn1Header struct {
	Number       int64
	PreviousHash []byte
	DataHash     []byte
}
// Bytes returns the ASN.1 marshaled representation of the block header.
func (b *BlockHeader) Bytes() []byte {
	asn1Header := asn1Header{
		PreviousHash: b.PreviousHash,
		DataHash:     b.DataHash,
	}
	if b.Number > uint64(math.MaxInt64) {
		panic(fmt.Errorf("Golang does not currently support encoding uint64 to asn1"))
	} else {
		asn1Header.Number = int64(b.Number)
	}
	result, err := asn1.Marshal(asn1Header)
	if err != nil {
		// Errors should only arise for types which cannot be encoded, since the
		// BlockHeader type is known a-priori to contain only encodable types, an
		// error here is fatal and should not be propogated
		panic(err)
	}
	return result
}
// Hash returns the hash of the block header.
// XXX This method will be removed shortly to allow for confgurable hashing algorithms
func (b *BlockHeader) Hash() []byte {
	return ComputeSHA256(b.Bytes()) //SOURCE:util.ComputeSHA256
}
// Bytes returns a deterministically serialized version of the BlockData
// eventually, this should be replaced with a true Merkle tree construction,
// but for the moment, we assume a Merkle tree of infinite width (uint32_max)
// which degrades to a flat hash
func (b *BlockData) Bytes() []byte {
	return ConcatenateBytes(b.Data...) //SOURCE:util.ConcatenateBytes
}
// Hash returns the hash of the marshaled representation of the block data.
func (b *BlockData) Hash() []byte {
	return ComputeSHA256(b.Bytes()) //SOURCE:util.ComputeSHA256
}

/*** fabric/common/genesis/genesis.go ***/
// Factory facilitates the creation of genesis blocks.
type Factory interface {
	// Block returns a genesis block for a given channel ID.
	Block(channelID string) (*Block, error) //SOURCE:cb.Block
}
type factory struct {
	template Template //SOURCE:configtx.Template
}
// NewFactoryImpl creates a new Factory.
func NewFactoryImpl(template Template) Factory { //SOURCE:configtx.Template
	return &factory{template: template}
}
// Block constructs and returns a genesis block for a given channel ID.
func (f *factory) Block(channelID string) (*Block, error) { //SOURCE:cb.Block
	configEnv, err := f.template.Envelope(channelID)
	if err != nil {
		return nil, err
	}
	configUpdate := &ConfigUpdate{} //SOURCE:cb.ConfigUpdate
	err = proto.Unmarshal(configEnv.ConfigUpdate, configUpdate)
	if err != nil {
		return nil, err
	}
	payloadChannelHeader := MakeChannelHeader(HeaderType_CONFIG, msgVersion, channelID, epoch) //SOURCE:utils.MakeChannelHeader //SOURCE:cb.HeaderType_CONFIG
	payloadSignatureHeader := MakeSignatureHeader(nil, CreateNonceOrPanic()) //SOURCE:utils.MakeSignatureHeader //SOURCE:utils.CreateNonceOrPanic
	SetTxID(payloadChannelHeader, payloadSignatureHeader) //SOURCE:utils.SetTxID
	payloadHeader := MakePayloadHeader(payloadChannelHeader, payloadSignatureHeader) //SOURCE:utils.MakePayloadHeader
	payload := &Payload{Header: payloadHeader, Data: MarshalOrPanic(&ConfigEnvelope{Config: &Config{ChannelGroup: configUpdate.WriteSet}})} //SOURCE:cb.Payload //SOURCE:utils.MarshalOrPanic //SOURCE:cb.ConfigEnvelope //SOURCE:cb.Config
	envelope := &Envelope{Payload: MarshalOrPanic(payload), Signature: nil} //SOURCE:cb.Envelope //SOURCE:utils.MarshalOrPanic

	block := NewBlock(0, nil) //SOURCE:cb.NewBlock
	block.Data = &BlockData{Data: [][]byte{MarshalOrPanic(envelope)}} //SOURCE:cb.BlockData
	block.Header.DataHash = block.Data.Hash()
	block.Metadata.Metadata[BlockMetadataIndex_LAST_CONFIG] = MarshalOrPanic(&Metadata{ //SOURCE:cb.BlockMetadataIndex_LAST_CONFIG //SOURCE:utils.MarshalOrPanic //SOURCE:cb.Metadata
		Value: MarshalOrPanic(&LastConfig{Index: 0}), //SOURCE:utils.MarshalOrPanic //SOURCE:cb.LastConfig
	})
	return block, nil
}

/*** fabric/common/configtx/tool/provisional/provisional.go ***/
// Generator can either create an orderer genesis block or config template
type Generator interface {
	BootstrapHelper
	// ChannelTemplate returns a template which can be used to help initialize a channel
	ChannelTemplate() Template //SOURCE:configtx.Template
	// GenesisBlockForChannel TODO
	GenesisBlockForChannel(channelID string) *Block //SOURCE:cb.Block
}
const (
	// ConsensusTypeSolo identifies the solo consensus implementation.
	ConsensusTypeSolo = "solo"
	// ConsensusTypeKafka identifies the Kafka-based consensus implementation.
	ConsensusTypeKafka = "kafka"
	// TestChainID is the default value of ChainID. It is used by all testing
	// networks. It it necessary to set and export this variable so that test
	// clients can connect without being rejected for targeting a chain which
	// does not exist.
	TestChainID = "testchainid"
	// BlockValidationPolicyKey TODO
	BlockValidationPolicyKey = "BlockValidation"
	// OrdererAdminsPolicy is the absolute path to the orderer admins policy
	OrdererAdminsPolicy = "/Channel/Orderer/Admins"
)
type bootstrapper struct {
	channelGroups     []*ConfigGroup //SOURCE:cb.ConfigGroup
	ordererGroups     []*ConfigGroup //SOURCE:cb.ConfigGroup
	applicationGroups []*ConfigGroup //SOURCE:cb.ConfigGroup
	consortiumsGroups []*ConfigGroup //SOURCE:cb.ConfigGroup
}
// New returns a new provisional bootstrap helper.
func New(conf *Profile) Generator { //SOURCE:genesisconfig.Profile
	bs := &bootstrapper{
		channelGroups: []*ConfigGroup{ //SOURCE:cb.ConfigGroup
			// Chain Config Types
			DefaultHashingAlgorithm(), //SOURCE:config.DefaultHashingAlgorithm
			DefaultBlockDataHashingStructure(), //SOURCE:config.DefaultBlockDataHashingStructure
			// Default policies
			TemplateImplicitMetaAnyPolicy([]string{}, ReadersPolicyKey), //SOURCE:policies.TemplateImplicitMetaAnyPolicy //SOURCE:configvaluesmsp.ReadersPolicyKey
			TemplateImplicitMetaAnyPolicy([]string{}, WritersPolicyKey), //SOURCE:policies.TemplateImplicitMetaAnyPolicy //SOURCE:configvaluesmsp.WritersPolicyKey
			TemplateImplicitMetaMajorityPolicy([]string{}, AdminsPolicyKey), //SOURCE:policies.TemplateImplicitMetaMajorityPolicy //SOURCE:configvaluesmsp.AdminsPolicyKey
		},
	}
	if conf.Orderer != nil {
		// Orderer addresses
		oa := TemplateOrdererAddresses(conf.Orderer.Addresses) //SOURCE:config.TemplateOrdererAddresses
		oa.Values[OrdererAddressesKey].ModPolicy = OrdererAdminsPolicy //SOURCE:config.OrdererAddressesKey
		bs.ordererGroups = []*ConfigGroup{ //SOURCE:cb.ConfigGroup
			oa,
			// Orderer Config Types
			TemplateConsensusType(conf.Orderer.OrdererType), //SOURCE:config.TemplateConsensusType
			TemplateBatchSize(&BatchSizeORDERER{ //SOURCE:config.TemplateBatchSize //WAS:BatchSize //SOURCE:ab.BatchSize
				MaxMessageCount:   conf.Orderer.BatchSize.MaxMessageCount,
				AbsoluteMaxBytes:  conf.Orderer.BatchSize.AbsoluteMaxBytes,
				PreferredMaxBytes: conf.Orderer.BatchSize.PreferredMaxBytes,
			}),
			TemplateBatchTimeout(conf.Orderer.BatchTimeout.String()), //SOURCE:config.TemplateBatchTimeout
			TemplateChannelRestrictions(conf.Orderer.MaxChannels), //SOURCE:config.TemplateChannelRestrictions
			// Initialize the default Reader/Writer/Admins orderer policies, as well as block validation policy
			TemplateImplicitMetaPolicyWithSubPolicy([]string{OrdererGroupKey}, BlockValidationPolicyKey, WritersPolicyKey, ImplicitMetaPolicy_ANY), //SOURCE:policies.TemplateImplicitMetaPolicyWithSubPolicy //SOURCE:config.OrdererGroupKey //SOURCE:configvaluesmsp.WritersPolicyKey //SOURCE:cb.ImplicitMetaPolicy_ANY
			TemplateImplicitMetaAnyPolicy([]string{OrdererGroupKey}, ReadersPolicyKey), //SOURCE:policies.TemplateImplicitMetaAnyPolicy //SOURCE:config.OrdererGroupKey //SOURCE:configvaluesmsp.ReadersPolicyKey
			TemplateImplicitMetaAnyPolicy([]string{OrdererGroupKey}, WritersPolicyKey), //SOURCE:policies.TemplateImplicitMetaAnyPolicy //SOURCE:config.OrdererGroupKey //SOURCE:configvaluesmsp.WritersPolicyKey
			TemplateImplicitMetaMajorityPolicy([]string{OrdererGroupKey}, AdminsPolicyKey), //SOURCE:policies.TemplateImplicitMetaMajorityPolicy //SOURCE:config.OrdererGroupKey //SOURCE:configvaluesmsp.AdminsPolicyKey
		}
		for _, org := range conf.Orderer.Organizations {
			mspConfig, err := GetVerifyingMspConfig(org.MSPDir, org.ID) //SOURCE:msp.GetVerifyingMspConfig
			if err != nil {
				logger.Panicf("1 - Error loading MSP configuration for org %s: %s", org.Name, err)
			}
			bs.ordererGroups = append(bs.ordererGroups,
				TemplateGroupMSPWithAdminRolePrincipal([]string{OrdererGroupKey, org.Name}, //SOURCE:configvaluesmsp.TemplateGroupMSPWithAdminRolePrincipal //SOURCE:config.OrdererGroupKey
					mspConfig, org.AdminPrincipal == AdminRoleAdminPrincipal, //SOURCE:genesisconfig.AdminRoleAdminPrincipal
				),
			)
		}
		switch conf.Orderer.OrdererType {
		case ConsensusTypeSolo:
		case ConsensusTypeKafka:
			bs.ordererGroups = append(bs.ordererGroups, TemplateKafkaBrokers(conf.Orderer.Kafka.Brokers)) //SOURCE:config.TemplateKafkaBrokers
		default:
			panic(fmt.Errorf("Wrong consenter type value given: %s", conf.Orderer.OrdererType))
		}
	}

	if conf.Application != nil {
		bs.applicationGroups = []*ConfigGroup{ //SOURCE:cb.ConfigGroup
			// Initialize the default Reader/Writer/Admins application policies
			TemplateImplicitMetaAnyPolicy([]string{ApplicationGroupKey}, ReadersPolicyKey), //SOURCE:policies.TemplateImplicitMetaAnyPolicy //SOURCE:config.ApplicationGroupKey //SOURCE:configvaluesmsp.ReadersPolicyKey
			TemplateImplicitMetaAnyPolicy([]string{ApplicationGroupKey}, WritersPolicyKey), //SOURCE:policies.TemplateImplicitMetaAnyPolicy //SOURCE:config.ApplicationGroupKey //SOURCE:configvaluesmsp.WritersPolicyKey
			TemplateImplicitMetaMajorityPolicy([]string{ApplicationGroupKey}, AdminsPolicyKey), //SOURCE:policies.TemplateImplicitMetaMajorityPolicy //SOURCE:config.ApplicationGroupKey //SOURCE:configvaluesmspv.AdminsPolicyKey
		}
		for _, org := range conf.Application.Organizations {
			mspConfig, err := GetVerifyingMspConfig(org.MSPDir, org.ID) //SOURCE:msp.GetVerifyingMspConfig
			if err != nil {
				logger.Panicf("2- Error loading MSP configuration for org %s: %s", org.Name, err)
			}
			bs.applicationGroups = append(bs.applicationGroups,
				TemplateGroupMSPWithAdminRolePrincipal([]string{ApplicationGroupKey, org.Name}, //SOURCE:configvaluesmsp.TemplateGroupMSPWithAdminRolePrincipal //SOURCE:config.ApplicationGroupKey
					mspConfig, org.AdminPrincipal == AdminRoleAdminPrincipal, //SOURCE:genesisconfig.AdminRoleAdminPrincipal
				),
			)
			var anchorProtos []*AnchorPeerPROTOS //WAS:AnchorPeer //SOURCE:pb.AnchorPeer
			for _, anchorPeer := range org.AnchorPeers {
				anchorProtos = append(anchorProtos, &AnchorPeerPROTOS{ //WAS:AnchorPeer //SOURCE:pb.AnchorPeer
					Host: anchorPeer.Host,
					Port: int32(anchorPeer.Port),
				})
			}
			bs.applicationGroups = append(bs.applicationGroups, TemplateAnchorPeers(org.Name, anchorProtos)) //SOURCE:config.TemplateAnchorPeers
		}
	}

	if conf.Consortiums != nil {
		tcg := TemplateConsortiumsGroup() //SOURCE:config.TemplateConsortiumsGroup
		tcg.Groups[ConsortiumsGroupKey].ModPolicy = OrdererAdminsPolicy //SOURCE:config.ConsortiumsGroupKey
		// Fix for https://jira.hyperledger.org/browse/FAB-4373
		// Note, AcceptAllPolicy in this context, does not grant any unrestricted
		// access, but allows the /Channel/Admins policy to evaluate to true
		// for the ordering system channel while set to MAJORITY with the addition
		// to the successful evaluation of the /Channel/Orderer/Admins policy (which
		// is not AcceptAll
		tcg.Groups[ConsortiumsGroupKey].Policies[AdminsPolicyKey] = &ConfigPolicy{ //SOURCE:config.ConsortiumsGroupKey //SOURCE:configvaluesmsp.AdminsPolicyKey //SOURCE:cb.ConfigPolicy
			Policy: &Policy{ //SOURCE:cb.Policy
				Type:  int32(Policy_SIGNATURE), //SOURCE:ccb.Policy_SIGNATURE
				Value: MarshalOrPanic(AcceptAllPolicy), //SOURCE:utils.MarshalOrPanic //SOURCE:cauthdsl.AcceptAllPolicy
			},
			ModPolicy: OrdererAdminsPolicy,
		}
		bs.consortiumsGroups = append(bs.consortiumsGroups, tcg)
		for consortiumName, consortium := range conf.Consortiums {
			cg := TemplateConsortiumChannelCreationPolicy(consortiumName, ImplicitMetaPolicyWithSubPolicy( //SOURCE:config.TemplateConsortiumChannelCreationPolicy //SOURCE:policies.ImplicitMetaPolicyWithSubPolicy
				AdminsPolicyKey, //SOURCE:configvaluesmsp.AdminsPolicyKey
				ImplicitMetaPolicy_ANY, //SOURCE:cb.ImplicitMetaPolicy_ANY
			).Policy)
			cg.Groups[ConsortiumsGroupKey].Groups[consortiumName].ModPolicy = OrdererAdminsPolicy //SOURCE:config.ConsortiumsGroupKey
			cg.Groups[ConsortiumsGroupKey].Groups[consortiumName].Values[ChannelCreationPolicyKey].ModPolicy = OrdererAdminsPolicy //SOURCE:config.ConsortiumsGroupKey //SOURCE:config.ChannelCreationPolicyKey
			bs.consortiumsGroups = append(bs.consortiumsGroups, cg)
			for _, org := range consortium.Organizations {
				mspConfig, err := GetVerifyingMspConfig(org.MSPDir, org.ID) //SOURCE:msp.GetVerifyingMspConfig
				if err != nil {
					logger.Panicf("3 - Error loading MSP configuration for org %s: %s", org.Name, err)
				}
				bs.consortiumsGroups = append(bs.consortiumsGroups,
					TemplateGroupMSPWithAdminRolePrincipal( //SOURCE:configvaluesmsp.TemplateGroupMSPWithAdminRolePrincipal
						[]string{ConsortiumsGroupKey, consortiumName, org.Name}, //SOURCE:config.ConsortiumsGroupKey
						mspConfig, org.AdminPrincipal == AdminRoleAdminPrincipal, //SOURCE:genesisconfig.AdminRoleAdminPrincipal
					),
				)
			}
		}
	}
	return bs
}
// ChannelTemplate TODO
func (bs *bootstrapper) ChannelTemplate() Template { //SOURCE:configtx.Template
	return NewModPolicySettingTemplate( //SOURCE:configtx.NewSimpleTemplate
		AdminsPolicyKey, //SOURCE:configvaluesmsp.AdminsPolicyKey
		NewCompositeTemplate( //SOURCE:configtx.NewSimpleTemplate
			NewSimpleTemplate(bs.channelGroups...), //SOURCE:configtx.NewSimpleTemplate
			NewSimpleTemplate(bs.ordererGroups...), //SOURCE:configtx.NewSimpleTemplate
			NewSimpleTemplate(bs.applicationGroups...), //SOURCE:configtx.NewSimpleTemplate
		),
	)
}
// GenesisBlock TODO Deprecate and remove
func (bs *bootstrapper) GenesisBlock() *Block { //SOURCE:cb.Block
	block, err := NewFactoryImpl( //SOURCE:genesis.NewFactoryImpl
		NewModPolicySettingTemplate( //SOURCE:configtx.NewModPolicySettingTemplate
			AdminsPolicyKey, //SOURCE:configvaluesmsp.AdminsPolicyKey
			NewCompositeTemplate( //SOURCE:configtx.NewCompositeTemplate
				NewSimpleTemplate(bs.consortiumsGroups...), //SOURCE:configtx.NewSimpleTemplate
				bs.ChannelTemplate(),
			),
		),
	).Block(TestChainID)

	if err != nil {
		panic(err)
	}
	return block
}
// GenesisBlockForChannel TODO
func (bs *bootstrapper) GenesisBlockForChannel(channelID string) *Block { //SOURCE:cb.Block
	block, err := NewFactoryImpl( //SOURCE:genesis.NewFactoryImpl
		NewModPolicySettingTemplate( //SOURCE:configtx.NewModPolicySettingTemplate
			AdminsPolicyKey, //SOURCE:configvaluesmsp.AdminsPolicyKey
			NewCompositeTemplate( //SOURCE:configtx.NewCompositeTemplate
				NewSimpleTemplate(bs.consortiumsGroups...), //SOURCE:configtx.NewSimpleTemplate
				bs.ChannelTemplate(),
			),
		),
	).Block(channelID)

	if err != nil {
		panic(err)
	}
	return block
}

/*** fabric/common/flogging/logging.go ***/
var (
	loggerFLOGGING *logging.Logger //WAS:logger
	defaultOutput *os.File
	modules          map[string]string // Holds the map of all modules and their respective log level
	peerStartModules map[string]string
	lock sync.RWMutex
	once sync.Once
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
	l := logging.MustGetLogger(module)
	lock.Lock()
	defer lock.Unlock()
	modules[module] = GetModuleLevel(module)
	return l
}

/*** fabric/common/policies/implicitmeta.go ***/
type implicitMetaPolicyPOLICIES struct { //WAS:implicitMetaPolicy
	conf        *ImplicitMetaPolicy //SOURCE:cb.ImplicitMetaPolicy
	threshold   int
	subPolicies []PolicyPOLICIES //WAS:Policy
}
// NewPolicy creates a new policy based on the policy bytes
func newImplicitMetaPolicy(data []byte) (*implicitMetaPolicyPOLICIES, error) { //WAS:implicitMetaPolicy
	imp := &ImplicitMetaPolicy{} //SOURCE:cb.ImplicitMetaPolicy
	if err := proto.Unmarshal(data, imp); err != nil {
		return nil, fmt.Errorf("Error unmarshaling to ImplicitMetaPolicy: %s", err)
	}
	return &implicitMetaPolicyPOLICIES{ //WAS:implicitMetaPolicy
		conf: imp,
	}, nil
}
func (imp *implicitMetaPolicyPOLICIES) initialize(config *policyConfig) { //WAS:implicitMetaPolicy
	imp.subPolicies = make([]PolicyPOLICIES, len(config.managers)) //WAS:Policy
	i := 0
	for _, manager := range config.managers {
		imp.subPolicies[i], _ = manager.GetPolicy(imp.conf.SubPolicy)
		i++
	}
	switch imp.conf.Rule {
	case ImplicitMetaPolicy_ANY: //SOURCE:cb.ImplicitMetaPolicy_ANY
		imp.threshold = 1
	case ImplicitMetaPolicy_ALL: //SOURCE:cb.ImplicitMetaPolicy_ALL
		imp.threshold = len(imp.subPolicies)
	case ImplicitMetaPolicy_MAJORITY: //SOURCE:cb.ImplicitMetaPolicy_MAJORITY
		imp.threshold = len(imp.subPolicies)/2 + 1
	}
	// In the special case that there are no policies, consider 0 to be a majority or any
	if len(imp.subPolicies) == 0 {
		imp.threshold = 0
	}
}
// Evaluate takes a set of SignedData and evaluates whether this set of signatures satisfies the policy
func (imp *implicitMetaPolicyPOLICIES) Evaluate(signatureSet []*SignedData) error { //WAS:implicitMetaPolicy //SOURCE:cb.SignedData
	remaining := imp.threshold
	for _, policy := range imp.subPolicies {
		if policy.Evaluate(signatureSet) == nil {
			remaining--
			if remaining == 0 {
				return nil
			}
		}
	}
	if remaining == 0 {
		return nil
	}
	return fmt.Errorf("Failed to reach implicit threshold of %d sub-policies, required %d remaining", imp.threshold, remaining)
}

/*** fabric/protos/common/signed_data.go ***/
// SignedData is used to represent the general triplet required to verify a signature
// This is intended to be generic across crypto schemes, while most crypto schemes will
// include the signing identity and a nonce within the Data, this is left to the crypto
// implementation
type SignedData struct {
	Data      []byte
	Identity  []byte
	Signature []byte
}

/*** fabric/common/policies/policy.go ***/
const (
	// // Path separator is used to separate policy names in paths //REDECLARATION
	// PathSeparator = "/"
	// ChannelPrefix is used in the path of standard channel policy managers
	ChannelPrefix = "Channel"
	// ApplicationPrefix is used in the path of standard application policy paths
	ApplicationPrefix = "Application"
	// OrdererPrefix is used in the path of standard orderer policy paths
	OrdererPrefix = "Orderer"
	// ChannelReaders is the label for the channel's readers policy (encompassing both orderer and application readers)
	ChannelReaders = PathSeparator + ChannelPrefix + PathSeparator + "Readers"
	// ChannelWriters is the label for the channel's writers policy (encompassing both orderer and application writers)
	ChannelWriters = PathSeparator + ChannelPrefix + PathSeparator + "Writers"
	// ChannelApplicationReaders is the label for the channel's application readers policy
	ChannelApplicationReaders = PathSeparator + ChannelPrefix + PathSeparator + ApplicationPrefix + PathSeparator + "Readers"
	// ChannelApplicationWriters is the label for the channel's application writers policy
	ChannelApplicationWriters = PathSeparator + ChannelPrefix + PathSeparator + ApplicationPrefix + PathSeparator + "Writers"
	// ChannelApplicationAdmins is the label for the channel's application admin policy
	ChannelApplicationAdmins = PathSeparator + ChannelPrefix + PathSeparator + ApplicationPrefix + PathSeparator + "Admins"
	// BlockValidation is the label for the policy which should validate the block signatures for the channel
	BlockValidation = PathSeparator + ChannelPrefix + PathSeparator + OrdererPrefix + PathSeparator + "BlockValidation"
)
// Policy is used to determine if a signature is valid
type PolicyPOLICIES interface {
	// Evaluate takes a set of SignedData and evaluates whether this set of signatures satisfies the policy
	Evaluate(signatureSet []*SignedData) error //SOURCE:cb.SignedData
}
// Manager is a read only subset of the policy ManagerImpl
type ManagerPOLICIES interface {
	// GetPolicy returns a policy and true if it was the policy requested, or false if it is the default policy
	GetPolicy(id string) (PolicyPOLICIES, bool) //WAS:Policy
	// Manager returns the sub-policy manager for a given path and whether it exists
	Manager(path []string) (ManagerPOLICIES, bool) //WAS:Manager
	// Basepath returns the basePath the manager was instantiated with
	BasePath() string
	// Policies returns all policy names defined in the manager
	PolicyNames() []string
}
// Proposer is the interface used by the configtx manager for policy management
type ProposerPOLICIES interface { //WAS:Proposer
	// BeginPolicyProposals starts a policy update transaction
	BeginPolicyProposals(tx interface{}, groups []string) ([]ProposerPOLICIES, error) //WAS:Proposer
	// ProposePolicy createss a pending policy update from a ConfigPolicy and returns the deserialized
	// value of the Policy representation
	ProposePolicy(tx interface{}, name string, policy *ConfigPolicy) (proto.Message, error) //SOURCE:cb.ConfigPolicy
	// RollbackProposals discards the pending policy updates
	RollbackProposals(tx interface{})
	// CommitProposals commits the pending policy updates
	CommitProposals(tx interface{})
	// PreCommit tests if a commit will apply
	PreCommit(tx interface{}) error
}
// Provider provides the backing implementation of a policy
type Provider interface {
	// NewPolicy creates a new policy based on the policy bytes
	NewPolicy(data []byte) (PolicyPOLICIES, proto.Message, error) //WAS:Policy
}
type policyConfig struct {
	policies map[string]PolicyPOLICIES //WAS:Policy
	managers map[string]*ManagerImpl
	imps     []*implicitMetaPolicyPOLICIES //WAS:implicitMetaPolicy
}
// ManagerImpl is an implementation of Manager and configtx.ConfigHandler
// In general, it should only be referenced as an Impl for the configtx.ConfigManager
type ManagerImpl struct {
	parent        *ManagerImpl
	basePath      string
	fqPrefix      string
	providers     map[int32]Provider
	config        *policyConfig
	pendingConfig map[interface{}]*policyConfig
	pendingLock   sync.RWMutex
	// SuppressSanityLogMessages when set to true will prevent the sanity checking log
	// messages.  Useful for novel cases like channel templates
	SuppressSanityLogMessages bool
}
// NewManagerImpl creates a new ManagerImpl with the given CryptoHelper
func NewManagerImpl(basePath string, providers map[int32]Provider) *ManagerImpl {
	_, ok := providers[int32(Policy_IMPLICIT_META)] //SOURCE:cb.Policy_IMPLICIT_META
	if ok {
		logger.Panicf("ImplicitMetaPolicy type must be provider by the policy manager")
	}
	return &ManagerImpl{
		basePath:  basePath,
		fqPrefix:  PathSeparator + basePath + PathSeparator,
		providers: providers,
		config: &policyConfig{
			policies: make(map[string]PolicyPOLICIES), //WAS:Policy
			managers: make(map[string]*ManagerImpl),
		},
		pendingConfig: make(map[interface{}]*policyConfig),
	}
}
type rejectPolicy string
func (rp rejectPolicy) Evaluate(signedData []*SignedData) error { //SOURCE:cb.SignedData
	return fmt.Errorf("No such policy type: %s", rp)
}
// Basepath returns the basePath the manager was instnatiated with
func (pm *ManagerImpl) BasePath() string {
	return pm.basePath
}
func (pm *ManagerImpl) PolicyNames() []string {
	policyNames := make([]string, len(pm.config.policies))
	i := 0
	for policyName := range pm.config.policies {
		policyNames[i] = policyName
		i++
	}
	return policyNames
}
// Manager returns the sub-policy manager for a given path and whether it exists
func (pm *ManagerImpl) Manager(path []string) (ManagerPOLICIES, bool) { //WAS:Manager
	if len(path) == 0 {
		return pm, true
	}
	m, ok := pm.config.managers[path[0]]
	if !ok {
		return nil, false
	}
	return m.Manager(path[1:])
}
// GetPolicy returns a policy and true if it was the policy requested, or false if it is the default reject policy
func (pm *ManagerImpl) GetPolicy(id string) (PolicyPOLICIES, bool) { //WAS:Policy
	if id == "" {
		logger.Errorf("Returning dummy reject all policy because no policy ID supplied")
		return rejectPolicy(id), false
	}
	var relpath string
	if strings.HasPrefix(id, PathSeparator) {
		if pm.parent != nil {
			return pm.parent.GetPolicy(id)
		}
		if !strings.HasPrefix(id, pm.fqPrefix) {
			if logger.IsEnabledFor(logging.DEBUG) {
				logger.Debugf("Requested policy from root manager with wrong basePath: %s, returning rejectAll", id)
			}
			return rejectPolicy(id), false
		}
		relpath = id[len(pm.fqPrefix):]
	} else {
		relpath = id
	}
	policy, ok := pm.config.policies[relpath]
	if !ok {
		if logger.IsEnabledFor(logging.DEBUG) {
			logger.Debugf("Returning dummy reject all policy because %s could not be found in /%s/%s", id, pm.basePath, relpath)
		}
		return rejectPolicy(relpath), false
	}
	if logger.IsEnabledFor(logging.DEBUG) {
		logger.Debugf("Returning policy %s for evaluation", relpath)
	}
	return policy, true
}
// BeginPolicies is used to start a new config proposal
func (pm *ManagerImpl) BeginPolicyProposals(tx interface{}, groups []string) ([]ProposerPOLICIES, error) { //WAS:Proposer
	pm.pendingLock.Lock()
	defer pm.pendingLock.Unlock()
	pendingConfig, ok := pm.pendingConfig[tx]
	if ok {
		logger.Panicf("Serious Programming error: cannot call begin multiply for the same proposal")
	}
	pendingConfig = &policyConfig{
		policies: make(map[string]PolicyPOLICIES), //WAS:Policy
		managers: make(map[string]*ManagerImpl),
	}
	pm.pendingConfig[tx] = pendingConfig
	managers := make([]ProposerPOLICIES, len(groups)) //WAS:Proposer
	for i, group := range groups {
		newManager := NewManagerImpl(group, pm.providers)
		newManager.parent = pm
		pendingConfig.managers[group] = newManager
		managers[i] = newManager
	}
	return managers, nil
}
// RollbackProposals is used to abandon a new config proposal
func (pm *ManagerImpl) RollbackProposals(tx interface{}) {
	pm.pendingLock.Lock()
	defer pm.pendingLock.Unlock()
	delete(pm.pendingConfig, tx)
}
// PreCommit is currently a no-op for the policy manager and always returns nil
func (pm *ManagerImpl) PreCommit(tx interface{}) error {
	return nil
}
// CommitProposals is used to commit a new config proposal
func (pm *ManagerImpl) CommitProposals(tx interface{}) {
	pm.pendingLock.Lock()
	defer pm.pendingLock.Unlock()
	pendingConfig, ok := pm.pendingConfig[tx]
	if !ok {
		logger.Panicf("Programming error, cannot call begin in the middle of a proposal")
	}
	if pendingConfig == nil {
		logger.Panicf("Programming error, cannot call commit without an existing proposal")
	}
	for managerPath, m := range pendingConfig.managers {
		for _, policyName := range m.PolicyNames() {
			fqKey := managerPath + PathSeparator + policyName
			pendingConfig.policies[fqKey], _ = m.GetPolicy(policyName)
			logger.Debugf("In commit adding relative sub-policy %s to %s", fqKey, pm.basePath)
		}
	}
	// Now that all the policies are present, initialize the meta policies
	for _, imp := range pendingConfig.imps {
		imp.initialize(pendingConfig)
	}
	pm.config = pendingConfig
	delete(pm.pendingConfig, tx)
	if pm.parent == nil && pm.basePath == ChannelPrefix && !pm.SuppressSanityLogMessages {
		for _, policyName := range []string{ChannelReaders, ChannelWriters} {
			_, ok := pm.GetPolicy(policyName)
			if !ok {
				logger.Warningf("Current configuration has no policy '%s', this will likely cause problems in production systems", policyName)
			} else {
				logger.Debugf("As expected, current configuration has policy '%s'", policyName)
			}
		}
		if _, ok := pm.config.managers[ApplicationPrefix]; ok {
			// Check for default application policies if the application component is defined
			for _, policyName := range []string{
				ChannelApplicationReaders,
				ChannelApplicationWriters,
				ChannelApplicationAdmins} {
				_, ok := pm.GetPolicy(policyName)
				if !ok {
					logger.Warningf("Current configuration has no policy '%s', this will likely cause problems in production systems", policyName)
				} else {
					logger.Debugf("As expected, current configuration has policy '%s'", policyName)
				}
			}
		}
		if _, ok := pm.config.managers[OrdererPrefix]; ok {
			for _, policyName := range []string{BlockValidation} {
				_, ok := pm.GetPolicy(policyName)
				if !ok {
					logger.Warningf("Current configuration has no policy '%s', this will likely cause problems in production systems", policyName)
				} else {
					logger.Debugf("As expected, current configuration has policy '%s'", policyName)
				}
			}
		}
	}
}
// ProposePolicy takes key, path, and ConfigPolicy and registers it in the proposed PolicyManager, or errors
// It also returns the deserialized policy value for tracking and inspection at the invocation side.
func (pm *ManagerImpl) ProposePolicy(tx interface{}, key string, configPolicy *ConfigPolicy) (proto.Message, error) { //SOURCE:cb.ConfigPolicy
	pm.pendingLock.RLock()
	pendingConfig, ok := pm.pendingConfig[tx]
	pm.pendingLock.RUnlock()
	if !ok {
		logger.Panicf("Serious Programming error: called Propose without Begin")
	}
	policy := configPolicy.Policy
	if policy == nil {
		return nil, fmt.Errorf("Policy cannot be nil")
	}
	var cPolicy PolicyPOLICIES //WAS:Policy
	var deserialized proto.Message
	if policy.Type == int32(Policy_IMPLICIT_META) { //SOURCE:cb.Policy_IMPLICIT_META
		imp, err := newImplicitMetaPolicy(policy.Value)
		if err != nil {
			return nil, err
		}
		pendingConfig.imps = append(pendingConfig.imps, imp)
		cPolicy = imp
		deserialized = imp.conf
	} else {
		provider, ok := pm.providers[int32(policy.Type)]
		if !ok {
			return nil, fmt.Errorf("Unknown policy type: %v", policy.Type)
		}
		var err error
		cPolicy, deserialized, err = provider.NewPolicy(policy.Value)
		if err != nil {
			return nil, err
		}
	}
	pendingConfig.policies[key] = cPolicy
	logger.Debugf("Proposed new policy %s for %s", key, pm.basePath)
	return deserialized, nil
}

/*** fabric/common/configtx/config.go ***/
type ConfigResult interface {
	JSON() string
}
func NewConfigResult(config *ConfigGroup, proposer Proposer) (ConfigResult, error) { //SOURCE:cb.ConfigGroup //SOURCE:api.Proposer
	return processConfig(config, proposer)
}
type configResult struct {
	tx                   interface{}
	groupName            string
	groupKey             string
	group                *ConfigGroup //SOURCE:cb.ConfigGroup
	valueHandler         ValueProposer //SOURCE:config.ValueProposer
	policyHandler        ProposerPOLICIES //WAS:Proposer //SOURCE:policies.Proposer
	subResults           []*configResult
	deserializedValues   map[string]proto.Message
	deserializedPolicies map[string]proto.Message
}
func (cr *configResult) JSON() string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	cr.subResults[0].bufferJSON(&buffer)
	buffer.WriteString("}")
	return buffer.String()
}
// bufferJSON takes a buffer and writes a JSON representation of the configResult into the buffer
// Note that we use some mildly ad-hoc JSON encoding because the proto documentation explicitly
// mentions that the encoding/json package does not correctly marshal proto objects, and we
// do not have a proto object (nor can one be defined) which presents the mixed-map style of
// keys mapping to different types of the config
func (cr *configResult) bufferJSON(buffer *bytes.Buffer) {
	jpb := &jsonpb.Marshaler{
		EmitDefaults: true,
		Indent:       "    ",
	}
	// "GroupName": {
	buffer.WriteString("\"")
	buffer.WriteString(cr.groupKey)
	buffer.WriteString("\": {")
	//    "Values": {
	buffer.WriteString("\"Values\": {")
	count := 0
	for key, value := range cr.group.Values {
		// "Key": {
		buffer.WriteString("\"")
		buffer.WriteString(key)
		buffer.WriteString("\": {")
		// 	"Version": "X",
		buffer.WriteString("\"Version\":\"")
		buffer.WriteString(fmt.Sprintf("%d", value.Version))
		buffer.WriteString("\",")
		//      "ModPolicy": "foo",
		buffer.WriteString("\"ModPolicy\":\"")
		buffer.WriteString(value.ModPolicy)
		buffer.WriteString("\",")
		//      "Value": protoAsJSON
		buffer.WriteString("\"Value\":")
		jpb.Marshal(buffer, cr.deserializedValues[key])
		// },
		buffer.WriteString("}")
		count++
		if count < len(cr.group.Values) {
			buffer.WriteString(",")
		}
	}
	//     },
	buffer.WriteString("},")
	count = 0
	//    "Policies": {
	buffer.WriteString("\"Policies\": {")
	for key, policy := range cr.group.Policies {
		// "Key": {
		buffer.WriteString("\"")
		buffer.WriteString(key)
		buffer.WriteString("\": {")
		// 	"Version": "X",
		buffer.WriteString("\"Version\":\"")
		buffer.WriteString(fmt.Sprintf("%d", policy.Version))
		buffer.WriteString("\",")
		//      "ModPolicy": "foo",
		buffer.WriteString("\"ModPolicy\":\"")
		buffer.WriteString(policy.ModPolicy)
		buffer.WriteString("\",")
		//      "Policy": {
		buffer.WriteString("\"Policy\":{")
		//          "PolicyType" :
		buffer.WriteString(fmt.Sprintf("\"PolicyType\":\"%d\",", policy.Policy.Type))
		//          "Policy" : policyAsJSON
		buffer.WriteString("\"Policy\":")
		jpb.Marshal(buffer, cr.deserializedPolicies[key])
		//      }
		// },
		buffer.WriteString("}}")
		count++
		if count < len(cr.group.Policies) {
			buffer.WriteString(",")
		}
	}
	//     },
	buffer.WriteString("},")
	//     "Groups": {
	count = 0
	buffer.WriteString("\"Groups\": {")
	for _, subResult := range cr.subResults {
		subResult.bufferJSON(buffer)
		count++
		if count < len(cr.subResults) {
			buffer.WriteString(",")
		}
	}
	//     }
	buffer.WriteString("}")
	//     }
	buffer.WriteString("}")
}
func (cr *configResult) preCommit() error {
	for _, subResult := range cr.subResults {
		err := subResult.preCommit()
		if err != nil {
			return err
		}
	}
	return cr.valueHandler.PreCommit(cr.tx)
}
func (cr *configResult) commit() {
	for _, subResult := range cr.subResults {
		subResult.commit()
	}
	cr.valueHandler.CommitProposals(cr.tx)
	cr.policyHandler.CommitProposals(cr.tx)
}
func (cr *configResult) rollback() {
	for _, subResult := range cr.subResults {
		subResult.rollback()
	}
	cr.valueHandler.RollbackProposals(cr.tx)
	cr.policyHandler.RollbackProposals(cr.tx)
}
// proposeGroup proposes a group configuration with a given handler
// it will in turn recursively call itself until all groups have been exhausted
// at each call, it updates the configResult to contain references to the handlers
// which have been invoked so that calling result.commit() or result.rollback() will
// appropriately cleanup
func proposeGroup(result *configResult) error {
	subGroups := make([]string, len(result.group.Groups))
	i := 0
	for subGroup := range result.group.Groups {
		subGroups[i] = subGroup
		i++
	}
	valueDeserializer, subValueHandlers, err := result.valueHandler.BeginValueProposals(result.tx, subGroups)
	if err != nil {
		return err
	}
	subPolicyHandlers, err := result.policyHandler.BeginPolicyProposals(result.tx, subGroups)
	if err != nil {
		return err
	}
	if len(subValueHandlers) != len(subGroups) || len(subPolicyHandlers) != len(subGroups) {
		return fmt.Errorf("Programming error, did not return as many handlers as groups %d vs %d vs %d", len(subValueHandlers), len(subGroups), len(subPolicyHandlers))
	}
	for key, value := range result.group.Values {
		msg, err := valueDeserializer.Deserialize(key, value.Value)
		if err != nil {
			result.rollback()
			return fmt.Errorf("Error deserializing key %s for group %s: %s", key, result.groupName, err)
		}
		result.deserializedValues[key] = msg
	}
	for key, policy := range result.group.Policies {
		policy, err := result.policyHandler.ProposePolicy(result.tx, key, policy)
		if err != nil {
			result.rollback()
			return err
		}
		result.deserializedPolicies[key] = policy
	}
	result.subResults = make([]*configResult, 0, len(subGroups))
	for i, subGroup := range subGroups {
		result.subResults = append(result.subResults, &configResult{
			tx:                   result.tx,
			groupKey:             subGroup,
			groupName:            result.groupName + "/" + subGroup,
			group:                result.group.Groups[subGroup],
			valueHandler:         subValueHandlers[i],
			policyHandler:        subPolicyHandlers[i],
			deserializedValues:   make(map[string]proto.Message),
			deserializedPolicies: make(map[string]proto.Message),
		})
		if err := proposeGroup(result.subResults[i]); err != nil {
			result.rollback()
			return err
		}
	}
	return nil
}
func processConfig(channelGroup *ConfigGroup, proposer Proposer) (*configResult, error) { //SOURCE:cb.ConfigGroup //SOURCE:api.Proposer
	helperGroup := NewConfigGroup() //SOURCE:cb.NewConfigGroup
	helperGroup.Groups[RootGroupKey] = channelGroup
	configResult := &configResult{
		group:         helperGroup,
		valueHandler:  proposer.ValueProposer(),
		policyHandler: proposer.PolicyProposer(),
	}
	err := proposeGroup(configResult)
	if err != nil {
		return nil, err
	}
	return configResult, nil
}
func (cm *configManager) processConfig(channelGroup *ConfigGroup) (*configResult, error) { //SOURCE:cb.ConfigGroup
	logger.Debugf("Beginning new config for channel %s", cm.current.channelID)
	configResult, err := processConfig(channelGroup, cm.initializer)
	if err != nil {
		return nil, err
	}
	err = configResult.preCommit()
	if err != nil {
		configResult.rollback()
		return nil, err
	}
	return configResult, nil
}

/*** fabric/common/config/root.go ***/
// Root acts as the object which anchors the rest of the config
// Note, yes, this is a stuttering name, but, the intent is to move
// this up one level at the end of refactoring
type Root struct {
	channel          *ChannelGroup
	mspConfigHandler *MSPConfigHandler //SOURCE:msp.MSPConfigHandler
}
// NewRoot creates a new instance of the Root
func NewRoot(mspConfigHandler *MSPConfigHandler) *Root { //SOURCE:msp.MSPConfigHandler
	return &Root{
		channel:          NewChannelGroup(mspConfigHandler),
		mspConfigHandler: mspConfigHandler,
	}
}
type failDeserializer struct{}
func (fd failDeserializer) Deserialize(key string, value []byte) (proto.Message, error) {
	return nil, fmt.Errorf("Programming error, this should never be invoked")
}
// BeginValueProposals is used to start a new config proposal
func (r *Root) BeginValueProposals(tx interface{}, groups []string) (ValueDeserializer, []ValueProposer, error) {
	if len(groups) != 1 {
		return nil, nil, fmt.Errorf("Root config only supports having one base group")
	}
	if groups[0] != ChannelGroupKey {
		return nil, nil, fmt.Errorf("Root group must have channel")
	}
	r.mspConfigHandler.BeginConfig(tx)
	return failDeserializer{}, []ValueProposer{r.channel}, nil
}
// RollbackConfig is used to abandon a new config proposal
func (r *Root) RollbackProposals(tx interface{}) {
	r.mspConfigHandler.RollbackProposals(tx)
}
// PreCommit is used to verify total configuration before commit
func (r *Root) PreCommit(tx interface{}) error {
	return r.mspConfigHandler.PreCommit(tx)
}
// CommitConfig is used to commit a new config proposal
func (r *Root) CommitProposals(tx interface{}) {
	r.mspConfigHandler.CommitProposals(tx)
}
// Channel returns the associated Channel level config
func (r *Root) Channel() *ChannelGroup {
	return r.channel
}
// Orderer returns the associated Orderer level config
func (r *Root) Orderer() *OrdererGroup {
	return r.channel.OrdererConfig()
}
// Application returns the associated Application level config
func (r *Root) Application() *ApplicationGroup {
	return r.channel.ApplicationConfig()
}
func (r *Root) Consortiums() *ConsortiumsGroup {
	return r.channel.ConsortiumsConfig()
}

/*** fabric/msp/mspmgrimpl.go ***/
type mspManagerImpl struct {
	// map that contains all MSPs that we have setup or otherwise added
	mspsMap map[string]MSP
	// error that might have occurred at startup
	up bool
}
// NewMSPManager returns a new MSP manager instance;
// note that this instance is not initialized until
// the Setup method is called
func NewMSPManager() MSPManager {
	return &mspManagerImpl{}
}
// Setup initializes the internal data structures of this manager and creates MSPs
func (mgr *mspManagerImpl) Setup(msps []MSP) error {
	if mgr.up {
		mspLogger.Infof("MSP manager already up")
		return nil
	}
	if msps == nil {
		return fmt.Errorf("Setup error: nil config object")
	}
	if len(msps) == 0 {
		return fmt.Errorf("Setup error: at least one MSP configuration item is required")
	}
	mspLogger.Debugf("Setting up the MSP manager (%d msps)", len(msps))
	// create the map that assigns MSP IDs to their manager instance - once
	mgr.mspsMap = make(map[string]MSP)
	for _, msp := range msps {
		// add the MSP to the map of active MSPs
		mspID, err := msp.GetIdentifier()
		if err != nil {
			return fmt.Errorf("Could not extract msp identifier, err %s", err)
		}
		mgr.mspsMap[mspID] = msp
	}
	mgr.up = true
	mspLogger.Debugf("MSP manager setup complete, setup %d msps", len(msps))
	return nil
}
// GetMSPs returns the MSPs that are managed by this manager
func (mgr *mspManagerImpl) GetMSPs() (map[string]MSP, error) {
	return mgr.mspsMap, nil
}
// DeserializeIdentity returns an identity given its serialized version supplied as argument
func (mgr *mspManagerImpl) DeserializeIdentity(serializedID []byte) (Identity, error) {
	// We first deserialize to a SerializedIdentity to get the MSP ID
	sId := &SerializedIdentity{} //SOURCE:msp.SerializedIdentity
	err := proto.Unmarshal(serializedID, sId)
	if err != nil {
		return nil, fmt.Errorf("Could not deserialize a SerializedIdentity, err %s", err)
	}
	// we can now attempt to obtain the MSP
	msp := mgr.mspsMap[sId.Mspid]
	if msp == nil {
		return nil, fmt.Errorf("MSP %s is unknown", sId.Mspid)
	}
	switch t := msp.(type) {
	case *bccspmsp:
		return t.deserializeIdentityInternal(sId.IdBytes)
	default:
		return t.DeserializeIdentity(serializedID)
	}
}

/*** fabric/common/config/msp/config.go ***/
type pendingMSPConfig struct {
	mspConfig *MSPConfig //SOURCE:mspprotos.MSPConfig
	msp       MSP //SOURCE:msp.MSP
}
type mspConfigStore struct {
	idMap       map[string]*pendingMSPConfig
	proposedMgr MSPManager //SOURCE:msp.MSPManager
}
// MSPConfigHandler
type MSPConfigHandler struct {
	pendingConfig map[interface{}]*mspConfigStore
	pendingLock   sync.RWMutex
	MSPManager //SOURCE:msp.MSPManager
}
func NewMSPConfigHandler() *MSPConfigHandler {
	return &MSPConfigHandler{
		pendingConfig: make(map[interface{}]*mspConfigStore),
	}
}
// BeginConfig called when a config proposal is begun
func (bh *MSPConfigHandler) BeginConfig(tx interface{}) {
	bh.pendingLock.Lock()
	defer bh.pendingLock.Unlock()
	_, ok := bh.pendingConfig[tx]
	if ok {
		panic("Programming error, called BeginConfig multiply for the same tx")
	}
	bh.pendingConfig[tx] = &mspConfigStore{
		idMap: make(map[string]*pendingMSPConfig),
	}
}
// RollbackProposals called when a config proposal is abandoned
func (bh *MSPConfigHandler) RollbackProposals(tx interface{}) {
	bh.pendingLock.Lock()
	defer bh.pendingLock.Unlock()
	delete(bh.pendingConfig, tx)
}
// CommitProposals called when a config proposal is committed
func (bh *MSPConfigHandler) CommitProposals(tx interface{}) {
	bh.pendingLock.Lock()
	defer bh.pendingLock.Unlock()
	pendingConfig, ok := bh.pendingConfig[tx]
	if !ok {
		panic("Programming error, called BeginConfig multiply for the same tx")
	}
	bh.MSPManager = pendingConfig.proposedMgr
	delete(bh.pendingConfig, tx)
}
// ProposeValue called when config is added to a proposal
func (bh *MSPConfigHandler) ProposeMSP(tx interface{}, mspConfig *MSPConfig) (MSP, error) { //SOURCE:mspprotos.MSPConfig //SOURCE:msp.MSP
	bh.pendingLock.RLock()
	pendingConfig, ok := bh.pendingConfig[tx]
	bh.pendingLock.RUnlock()
	if !ok {
		panic("Programming error, called BeginConfig multiply for the same tx")
	}
	// check that the type for that MSP is supported
	if mspConfig.Type != int32(FABRIC) { //SOURCE:msp.FABRIC
		return nil, fmt.Errorf("Setup error: unsupported msp type %d", mspConfig.Type)
	}
	// create the msp instance
	mspInst, err := NewBccspMsp() //SOURCE:msp.NewBccspMsp
	if err != nil {
		return nil, fmt.Errorf("Creating the MSP manager failed, err %s", err)
	}
	// set it up
	err = mspInst.Setup(mspConfig)
	if err != nil {
		return nil, fmt.Errorf("Setting up the MSP manager failed, err %s", err)
	}
	// add the MSP to the map of pending MSPs
	mspID, _ := mspInst.GetIdentifier()
	existingPendingMSPConfig, ok := pendingConfig.idMap[mspID]
	if ok && !reflect.DeepEqual(existingPendingMSPConfig.mspConfig, mspConfig) {
		return nil, fmt.Errorf("Attempted to define two different versions of MSP: %s", mspID)
	}
	pendingConfig.idMap[mspID] = &pendingMSPConfig{
		mspConfig: mspConfig,
		msp:       mspInst,
	}
	return mspInst, nil
}
// PreCommit instantiates the MSP manager
func (bh *MSPConfigHandler) PreCommit(tx interface{}) error {
	bh.pendingLock.RLock()
	pendingConfig, ok := bh.pendingConfig[tx]
	bh.pendingLock.RUnlock()
	if !ok {
		panic("Programming error, called PreCommit for tx which was not started")
	}
	if len(pendingConfig.idMap) == 0 {
		// Cannot instantiate an MSP manager with no MSPs
		return nil
	}
	mspList := make([]MSP, len(pendingConfig.idMap)) //SOURCE:msp.MSP
	i := 0
	for _, pendingMSP := range pendingConfig.idMap {
		mspList[i] = pendingMSP.msp
		i++
	}
	pendingConfig.proposedMgr = NewMSPManager() //SOURCE:msp.NewMSPManager
	err := pendingConfig.proposedMgr.Setup(mspList)
	return err
}

/*** fabric/common/cauthdsl/cauthdsl.go ***/
var cauthdslLogger = MustGetLogger("cauthdsl") //SOURCE:flogging.MustGetLogger
// deduplicate removes any duplicated identities while otherwise preserving identity order
func deduplicate(sds []*SignedData) []*SignedData { //SOURCE:cb.SignedData
	ids := make(map[string]struct{})
	result := make([]*SignedData, 0, len(sds)) //SOURCE:cb.SignedData
	for i, sd := range sds {
		if _, ok := ids[string(sd.Identity)]; ok {
			cauthdslLogger.Warningf("De-duplicating identity %x at index %d in signature set", sd.Identity, i)
		} else {
			result = append(result, sd)
			ids[string(sd.Identity)] = struct{}{}
		}
	}
	return result
}
// compile recursively builds a go evaluatable function corresponding to the policy specified, remember to call deduplicate on identities before
// passing them to this function for evaluation
func compile(policy *SignaturePolicy, identities []*MSPPrincipal, deserializer IdentityDeserializer) (func([]*SignedData, []bool) bool, error) { //SOURCE:cb.SignaturePolicy //SOURCE:mb.MSPPrincipal //SOURCE:msp.IdentityDeserializer //SOURCE:cb.SignedData
	if policy == nil {
		return nil, fmt.Errorf("Empty policy element")
	}
	switch t := policy.Type.(type) {
	case *SignaturePolicy_NOutOf_: //SOURCE:cb.SignaturePolicy_NOutOf_
		policies := make([]func([]*SignedData, []bool) bool, len(t.NOutOf.Rules)) //SOURCE:cb.SignedData
		for i, policy := range t.NOutOf.Rules {
			compiledPolicy, err := compile(policy, identities, deserializer)
			if err != nil {
				return nil, err
			}
			policies[i] = compiledPolicy
		}
		return func(signedData []*SignedData, used []bool) bool { //SOURCE:cb.SignedData
			grepKey := time.Now().UnixNano()
			cauthdslLogger.Debugf("%p gate %d evaluation starts", signedData, grepKey)
			verified := int32(0)
			_used := make([]bool, len(used))
			for _, policy := range policies {
				copy(_used, used)
				if policy(signedData, _used) {
					verified++
					copy(used, _used)
				}
			}
			if verified >= t.NOutOf.N {
				cauthdslLogger.Debugf("%p gate %d evaluation succeeds", signedData, grepKey)
			} else {
				cauthdslLogger.Debugf("%p gate %d evaluation fails", signedData, grepKey)
			}
			return verified >= t.NOutOf.N
		}, nil
	case *SignaturePolicy_SignedBy: //SOURCE:cb.SignaturePolicy_SignedBy
		if t.SignedBy < 0 || t.SignedBy >= int32(len(identities)) {
			return nil, fmt.Errorf("identity index out of range, requested %v, but identies length is %d", t.SignedBy, len(identities))
		}
		signedByID := identities[t.SignedBy]
		return func(signedData []*SignedData, used []bool) bool { //SOURCE:cb.SignedData
			cauthdslLogger.Debugf("%p signed by %d principal evaluation starts (used %v)", signedData, t.SignedBy, used)
			for i, sd := range signedData {
				if used[i] {
					cauthdslLogger.Debugf("%p skipping identity %d because it has already been used", signedData, i)
					continue
				}
				if cauthdslLogger.IsEnabledFor(logging.DEBUG) {
					// Unlike most places, this is a huge print statement, and worth checking log level before create garbage
					cauthdslLogger.Debugf("%p processing identity %d with bytes of %x", signedData, i, sd.Identity)
				}
				identity, err := deserializer.DeserializeIdentity(sd.Identity)
				if err != nil {
					cauthdslLogger.Errorf("Principal deserialization failure (%s) for identity %x", err, sd.Identity)
					continue
				}
				err = identity.SatisfiesPrincipal(signedByID)
				if err != nil {
					cauthdslLogger.Debugf("%p identity %d does not satisfy principal: %s", signedData, i, err)
					continue
				}
				cauthdslLogger.Debugf("%p principal matched by identity %d", signedData, i)
				err = identity.Verify(sd.Data, sd.Signature)
				if err != nil {
					cauthdslLogger.Debugf("%p signature for identity %d is invalid: %s", signedData, i, err)
					continue
				}
				cauthdslLogger.Debugf("%p principal evaluation succeeds for identity %d", signedData, i)
				used[i] = true
				return true
			}
			cauthdslLogger.Debugf("%p principal evaluation fails", signedData)
			return false
		}, nil
	default:
		return nil, fmt.Errorf("Unknown type: %T:%v", t, t)
	}
}

/*** fabric/common/cauthdsl/policy.go ***/
type provider struct {
	deserializer IdentityDeserializer //SOURCE:msp.IdentityDeserializer
}
// NewProviderImpl provides a policy generator for cauthdsl type policies
func NewPolicyProvider(deserializer IdentityDeserializer) Provider { //SOURCE:msp.IdentityDeserializer //SOURCE:policies.Provider
	return &provider{
		deserializer: deserializer,
	}
}
// NewPolicy creates a new policy based on the policy bytes
func (pr *provider) NewPolicy(data []byte) (PolicyPOLICIES, proto.Message, error) { //WAS:Policy //SOURCE:policies.Policy
	sigPolicy := &SignaturePolicyEnvelope{} //SOURCE:cb.SignaturePolicyEnvelope
	if err := proto.Unmarshal(data, sigPolicy); err != nil {
		return nil, nil, fmt.Errorf("Error unmarshaling to SignaturePolicy: %s", err)
	}
	if sigPolicy.Version != 0 {
		return nil, nil, fmt.Errorf("This evaluator only understands messages of version 0, but version was %d", sigPolicy.Version)
	}
	compiled, err := compile(sigPolicy.Rule, sigPolicy.Identities, pr.deserializer)
	if err != nil {
		return nil, nil, err
	}
	return &policy{
		evaluator: compiled,
	}, sigPolicy, nil
}
type policy struct {
	evaluator func([]*SignedData, []bool) bool //SOURCE:cb.SignedData
}
// Evaluate takes a set of SignedData and evaluates whether this set of signatures satisfies the policy
func (p *policy) Evaluate(signatureSet []*SignedData) error { //SOURCE:cb.SignedData
	if p == nil {
		return fmt.Errorf("No such policy")
	}
	ok := p.evaluator(deduplicate(signatureSet), make([]bool, len(signatureSet)))
	if !ok {
		return errors.New("Failed to authenticate policy")
	}
	return nil
}

/*** fabric/common/configtx/initializer.go ***/
type resources struct {
	policyManager    *ManagerImpl //SOURCE:policies.ManagerImpl
	configRoot       *Root //SOURCE:config.Root
	mspConfigHandler *MSPConfigHandler //SOURCE:configtxmsp.MSPConfigHandler
}
// PolicyManager returns the policies.Manager for the chain
func (r *resources) PolicyManager() ManagerPOLICIES { //WAS:Manager //SOURCE:policies.Manager
	return r.policyManager
}
// ChannelConfig returns the api.ChannelConfig for the chain
func (r *resources) ChannelConfig() Channel { //SOURCE:config.Channel
	return r.configRoot.Channel()
}
// OrdererConfig returns the api.OrdererConfig for the chain
func (r *resources) OrdererConfig() (OrdererCOMMONCONFIG, bool) { //WAS:Orderer //SOURCE:config.Orderer
	result := r.configRoot.Orderer()
	if result == nil {
		return nil, false
	}
	return result, true
}
// ApplicationConfig returns the api.ApplicationConfig for the chain
func (r *resources) ApplicationConfig() (ApplicationCOMMONCONFIG, bool) { //WAS:Application //SOURCE:config.Application
	result := r.configRoot.Application()
	if result == nil {
		return nil, false
	}
	return result, true
}
// ConsortiumsConfig returns the api.ConsortiumsConfig for the chain and whether or not
// this channel contains consortiums config
func (r *resources) ConsortiumsConfig() (ConsortiumsCOMMONCONFIG, bool) { //WAS:Consortiums //SOURCE:config.Consortiums
	result := r.configRoot.Consortiums()
	if result == nil {
		return nil, false
	}
	return result, true
}
// MSPManager returns the msp.MSPManager for the chain
func (r *resources) MSPManager() MSPManager { //SOURCE:msp.MSPManager
	return r.mspConfigHandler
}
func newResources() *resources {
	mspConfigHandler := NewMSPConfigHandler() //SOURCE:configtxmsp.NewMSPConfigHandler
	policyProviderMap := make(map[int32]Provider) //SOURCE:policies.Provider
	for pType := range Policy_PolicyType_name { //SOURCE:cb.Policy_PolicyType_name
		rtype := Policy_PolicyType(pType) //SOURCE:cb.Policy_PolicyType
		switch rtype {
		case Policy_UNKNOWN: //SOURCE:cb.Policy_UNKNOWN
			// Do not register a handler
		case Policy_SIGNATURE: //SOURCE:cb.Policy_SIGNATURE
			policyProviderMap[pType] = NewPolicyProvider(mspConfigHandler) //SOURCE:cauthdsl.NewPolicyProvider
		case Policy_MSP: //SOURCE:cb.Policy_MSP
			// Add hook for MSP Handler here
		}
	}
	return &resources{
		policyManager:    NewManagerImpl(RootGroupKey, policyProviderMap), //SOURCE:policies.NewManagerImpl
		configRoot:       NewRoot(mspConfigHandler), //SOURCE:config.NewRoot
		mspConfigHandler: mspConfigHandler,
	}
}
type policyProposerRoot struct {
	policyManager ProposerPOLICIES //WAS:Proposer //SOURCE:policies.Proposer
}
// BeginPolicyProposals is used to start a new config proposal
func (p *policyProposerRoot) BeginPolicyProposals(tx interface{}, groups []string) ([]ProposerPOLICIES, error) { //WAS:Proposer //SOURCE:policies.Proposer
	if len(groups) != 1 {
		logger.Panicf("Initializer only supports having one root group")
	}
	return []ProposerPOLICIES{p.policyManager}, nil //WAS:Proposer //SOURCE:policies.Proposer
}
func (i *policyProposerRoot) ProposePolicy(tx interface{}, key string, policy *ConfigPolicy) (proto.Message, error) { //SOURCE:cb.ConfigPolicy
	return nil, fmt.Errorf("Programming error, this should never be invoked")
}
// PreCommit is a no-op and returns nil
func (i *policyProposerRoot) PreCommit(tx interface{}) error {
	return nil
}
// RollbackConfig is used to abandon a new config proposal
func (i *policyProposerRoot) RollbackProposals(tx interface{}) {}
// CommitConfig is used to commit a new config proposal
func (i *policyProposerRoot) CommitProposals(tx interface{}) {}
type initializer struct {
	*resources
	ppr *policyProposerRoot
}
// NewInitializer creates a chain initializer for the basic set of common chain resources
func NewInitializer() Initializer { //SOURCE:api.Initializer
	resources := newResources()
	return &initializer{
		resources: resources,
		ppr: &policyProposerRoot{
			policyManager: resources.policyManager,
		},
	}
}
func (i *initializer) PolicyProposer() ProposerPOLICIES { //WAS:Proposer //SOURCE:policies.Proposer
	return i.ppr
}
func (i *initializer) ValueProposer() ValueProposer { //SOURCE:config.ValueProposer
	return i.resources.configRoot
}

/*** fabric/common/configtx/tool/configtxgen/metadata/metadata.go ***/
// Package version
var Version string
// Program name
const ProgramName = "configtxgen"
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
*
ORIGINAL CONFIGTXGEN FILE
*
*
*
*/
var exitCode = 0
var logger = MustGetLogger("common/configtx/tool") //SOURCE:flogging.MustGetLogger

func doOutputBlock(config *Profile, channelID string, outputBlock string) error { //SOURCE:genesisconfig.Profile
	pgen := New(config) //SOURCE:provisional.New
	logger.Info("Generating genesis block")
	if config.Orderer == nil {
		return fmt.Errorf("config does not contain an Orderers section, necessary for all config blocks, aborting")
	}
	if config.Consortiums == nil {
		logger.Warning("Genesis block does not contain a consortiums group definition.  This block cannot be used for orderer bootstrap.")
	}
	genesisBlock := pgen.GenesisBlockForChannel(channelID)
	logger.Info("Writing genesis block")
	err := ioutil.WriteFile(outputBlock, MarshalOrPanic(genesisBlock), 0644) //SOURCE:utils.MarshalOrPanic
	if err != nil {
		return fmt.Errorf("Error writing genesis block: %s", err)
	}
	return nil
}

func doOutputChannelCreateTx(conf *Profile, channelID string, outputChannelCreateTx string) error { //SOURCE:genesisconfig.Profile
	logger.Info("Generating new channel configtx")

	if conf.Application == nil {
		return fmt.Errorf("Cannot define a new channel with no Application section")
	}

	if conf.Consortium == "" {
		return fmt.Errorf("Cannot define a new channel with no Consortium value")
	}

	// XXX we ignore the non-application org names here, once the tool supports configuration updates
	// we should come up with a cleaner way to handle this, but leaving as is for the moment to not break
	// backwards compatibility
	var orgNames []string
	for _, org := range conf.Application.Organizations {
		orgNames = append(orgNames, org.Name)
	}
	configtx, err := MakeChainCreationTransaction(channelID, conf.Consortium, nil, orgNames...) //SOURCE:configtx.MakeChainCreationTransaction
	if err != nil {
		return fmt.Errorf("Error generating configtx: %s", err)
	}
	logger.Info("Writing new channel tx")
	err = ioutil.WriteFile(outputChannelCreateTx, MarshalOrPanic(configtx), 0644) //SOURCE:utils.MarshalOrPanic
	if err != nil {
		return fmt.Errorf("Error writing channel create tx: %s", err)
	}
	return nil
}

func doOutputAnchorPeersUpdate(conf *Profile, channelID string, outputAnchorPeersUpdate string, asOrg string) error { //SOURCE:genesisconfig.Profile
	logger.Info("Generating anchor peer update")
	if asOrg == "" {
		return fmt.Errorf("Must specify an organization to update the anchor peer for")
	}

	if conf.Application == nil {
		return fmt.Errorf("Cannot update anchor peers without an application section")
	}

	var org *Organization //SOURCE:genesisconfig.Organization
	for _, iorg := range conf.Application.Organizations {
		if iorg.Name == asOrg {
			org = iorg
		}
	}

	if org == nil {
		return fmt.Errorf("No organization name matching: %s", asOrg)
	}

	anchorPeers := make([]*AnchorPeerPROTOS, len(org.AnchorPeers)) //WAS:AnchorPeer //SOURCE:pb.AnchorPeer
	for i, anchorPeer := range org.AnchorPeers {
		anchorPeers[i] = &AnchorPeerPROTOS{ //WAS:AnchorPeer //SOURCE:pb.AnchorPeer
			Host: anchorPeer.Host,
			Port: int32(anchorPeer.Port),
		}
	}

	configGroup := TemplateAnchorPeers(org.Name, anchorPeers) //SOURCE:config.TemplateAnchorPeers
	configGroup.Groups[ApplicationGroupKey].Groups[org.Name].Values[AnchorPeersKey].ModPolicy = AdminsPolicyKey //SOURCE:config.ApplicationGroupKey //SOURCE:config.AnchorPeersKey //SOURCE:mspconfig.AdminsPolicyKey
	configUpdate := &ConfigUpdate{ //SOURCE:cb.ConfigUpdate
		ChannelId: channelID,
		WriteSet:  configGroup,
		ReadSet:   NewConfigGroup(), //SOURCE:cb.NewConfigGroup
	}

	// Add all the existing config to the readset
	configUpdate.ReadSet.Groups[ApplicationGroupKey] = NewConfigGroup() //SOURCE:config.ApplicationGroupKey //SOURCE:cb.NewConfigGroup
	configUpdate.ReadSet.Groups[ApplicationGroupKey].Version = 1 //SOURCE:config.ApplicationGroupKey
	configUpdate.ReadSet.Groups[ApplicationGroupKey].ModPolicy = AdminsPolicyKey //SOURCE:config.ApplicationGroupKey //SOURCE:mspconfig.AdminsPolicyKey
	configUpdate.ReadSet.Groups[ApplicationGroupKey].Groups[org.Name] = NewConfigGroup() //SOURCE:config.ApplicationGroupKey //SOURCE:cb.NewConfigGroup
	configUpdate.ReadSet.Groups[ApplicationGroupKey].Groups[org.Name].Values[MSPKey] = &ConfigValue{} //SOURCE:config.ApplicationGroupKey //SOURCE:config.MSPKey //SOURCE:cb.ConfigValue
	configUpdate.ReadSet.Groups[ApplicationGroupKey].Groups[org.Name].Policies[ReadersPolicyKey] = &ConfigPolicy{} //SOURCE:config.ApplicationGroupKey //SOURCE:mspconfig.ReadersPolicyKey //SOURCE:cb.ConfigPolicy
	configUpdate.ReadSet.Groups[ApplicationGroupKey].Groups[org.Name].Policies[WritersPolicyKey] = &ConfigPolicy{} //SOURCE:config.ApplicationGroupKey //SOURCE:mspconfig.WritersPolicyKey //SOURCE:cb.ConfigPolicy
	configUpdate.ReadSet.Groups[ApplicationGroupKey].Groups[org.Name].Policies[AdminsPolicyKey] = &ConfigPolicy{} //SOURCE:config.ApplicationGroupKey //SOURCE:mspconfig.AdminsPolicyKey //SOURCE:cb.ConfigPolicy

	// Add all the existing at the same versions to the writeset
	configUpdate.WriteSet.Groups[ApplicationGroupKey].Version = 1 //SOURCE:config.ApplicationGroupKey
	configUpdate.WriteSet.Groups[ApplicationGroupKey].ModPolicy = AdminsPolicyKey //SOURCE:config.ApplicationGroupKey //SOURCE:mspconfig.AdminsPolicyKey
	configUpdate.WriteSet.Groups[ApplicationGroupKey].Groups[org.Name].Version = 1 //SOURCE:config.ApplicationGroupKey
	configUpdate.WriteSet.Groups[ApplicationGroupKey].Groups[org.Name].ModPolicy = AdminsPolicyKey //SOURCE:config.ApplicationGroupKey //SOURCE:mspconfig.AdminsPolicyKey
	configUpdate.WriteSet.Groups[ApplicationGroupKey].Groups[org.Name].Values[MSPKey] = &ConfigValue{} //SOURCE:config.ApplicationGroupKey //SOURCE:config.MSPKey //SOURCE:cb.ConfigValue
	configUpdate.WriteSet.Groups[ApplicationGroupKey].Groups[org.Name].Policies[ReadersPolicyKey] = &ConfigPolicy{} //SOURCE:config.ApplicationGroupKey //SOURCE:mspconfig.AdminsPolicyKey //SOURCE:cb.ConfigPolicy
	configUpdate.WriteSet.Groups[ApplicationGroupKey].Groups[org.Name].Policies[WritersPolicyKey] = &ConfigPolicy{} //SOURCE:config.ApplicationGroupKey //SOURCE:mspconfig.AdminsPolicyKey //SOURCE:cb.ConfigPolicy
	configUpdate.WriteSet.Groups[ApplicationGroupKey].Groups[org.Name].Policies[AdminsPolicyKey] = &ConfigPolicy{} //SOURCE:config.ApplicationGroupKey //SOURCE:mspconfig.AdminsPolicyKey //SOURCE:cb.ConfigPolicy

	configUpdateEnvelope := &ConfigUpdateEnvelope{ //SOURCE:cb.ConfigUpdateEnvelope
		ConfigUpdate: MarshalOrPanic(configUpdate), //SOURCE:utils.MarshalOrPanic
	}

	update := &Envelope{ //SOURCE:cb.Envelope
		Payload: MarshalOrPanic(&Payload{ //SOURCE:utils.MarshalOrPanic //SOURCE:cb.Payload
			Header: &Header{ //SOURCE:cb.Header
				ChannelHeader: MarshalOrPanic(&ChannelHeader{ //SOURCE:utils.MarshalOrPanic //SOURCE:cb.ChannelHeader
					ChannelId: channelID,
					Type:      int32(HeaderType_CONFIG_UPDATE), //SOURCE:cb.HeaderType_CONFIG_UPDATE
				}),
			},
			Data: MarshalOrPanic(configUpdateEnvelope), //SOURCE:utils.MarshalOrPanic
		}),
	}

	logger.Info("Writing anchor peer update")
	err := ioutil.WriteFile(outputAnchorPeersUpdate, MarshalOrPanic(update), 0644) //SOURCE:utils.MarshalOrPanic
	if err != nil {
		return fmt.Errorf("Error writing channel anchor peer update: %s", err)
	}
	return nil
}

func doInspectBlock(inspectBlock string) error {
	logger.Info("Inspecting block")
	data, err := ioutil.ReadFile(inspectBlock)
	if err != nil {
		return fmt.Errorf("Could not read block %s", inspectBlock)
	}

	logger.Info("Parsing genesis block")
	block := &Block{} //SOURCE:cb.Block
	err = proto.Unmarshal(data, block)
	if err != nil {
		return fmt.Errorf("Error unmarshaling block: %s", err)
	}

	ctx, err := ExtractEnvelope(block, 0) //SOURCE:utils.ExtractEnvelope
	if err != nil {
		return fmt.Errorf("Error retrieving configtx from block: %s", err)
	}

	payload, err := UnmarshalPayload(ctx.Payload) //SOURCE:utils.UnmarshalPayload
	if err != nil {
		return fmt.Errorf("Error extracting configtx payload: %s", err)
	}

	if payload.Header == nil {
		return fmt.Errorf("Config block did not contain header")
	}

	header, err := UnmarshalChannelHeader(payload.Header.ChannelHeader) //SOURCE:utils.UnmarshalChannelHeader
	if err != nil {
		return fmt.Errorf("Error unmarshaling channel header: %s", err)
	}

	if header.Type != int32(HeaderType_CONFIG) { //SOURCE:cb.HeaderType_CONFIG
		return fmt.Errorf("Bad header type: %d", header.Type)
	}

	configEnvelope, err := UnmarshalConfigEnvelope(payload.Data) //SOURCE:configtx.UnmarshalConfigEnvelope
	if err != nil {
		return fmt.Errorf("Bad configuration envelope")
	}

	if configEnvelope.Config == nil {
		return fmt.Errorf("ConfigEnvelope contained no config")
	}

	configAsJSON, err := configGroupAsJSON(configEnvelope.Config.ChannelGroup)
	if err != nil {
		return err
	}

	fmt.Printf("Config for channel: %s at sequence %d\n", header.ChannelId, configEnvelope.Config.Sequence)
	fmt.Println(configAsJSON)

	return nil
}

func configGroupAsJSON(group *ConfigGroup) (string, error) { //SOURCE:cb.ConfigGroup
	configResult, err := NewConfigResult(group, NewInitializer()) //SOURCE:configtx.NewConfigResult //SOURCE:configtx.NewInitializer
	if err != nil {
		return "", fmt.Errorf("Error parsing config: %s", err)
	}

	buffer := &bytes.Buffer{}
	err = json.Indent(buffer, []byte(configResult.JSON()), "", "    ")
	if err != nil {
		return "", fmt.Errorf("Error in output JSON (usually a programming bug): %s", err)
	}
	return buffer.String(), nil
}

func doInspectChannelCreateTx(inspectChannelCreateTx string) error {
	logger.Info("Inspecting transaction")
	data, err := ioutil.ReadFile(inspectChannelCreateTx)
	if err != nil {
		return fmt.Errorf("could not read channel create tx: %s", err)
	}

	logger.Info("Parsing transaction")
	env, err := UnmarshalEnvelope(data) //SOURCE:utils.UnmarshalEnvelope
	if err != nil {
		return fmt.Errorf("Error unmarshaling envelope: %s", err)
	}

	payload, err := UnmarshalPayload(env.Payload) //SOURCE:utils.UnmarshalPayload
	if err != nil {
		return fmt.Errorf("Error extracting configtx payload: %s", err)
	}

	if payload.Header == nil {
		return fmt.Errorf("Config block did not contain header")
	}

	header, err := UnmarshalChannelHeader(payload.Header.ChannelHeader) //SOURCE:utils.UnmarshalChannelHeader
	if err != nil {
		return fmt.Errorf("Error unmarshaling channel header: %s", err)
	}

	if header.Type != int32(HeaderType_CONFIG_UPDATE) { //SOURCE:cb.HeaderType_CONFIG_UPDATE
		return fmt.Errorf("Bad header type: %d", header.Type)
	}

	configUpdateEnvelope, err := UnmarshalConfigUpdateEnvelope(payload.Data) //SOURCE:configtx.UnmarshalConfigUpdateEnvelope
	if err != nil {
		return fmt.Errorf("Bad ConfigUpdateEnvelope")
	}

	configUpdate, err := UnmarshalConfigUpdate(configUpdateEnvelope.ConfigUpdate) //SOURCE:configtx.UnmarshalConfigUpdate
	if err != nil {
		return fmt.Errorf("ConfigUpdateEnvelope contained no config")
	}

	if configUpdate.ChannelId != header.ChannelId {
		return fmt.Errorf("ConfigUpdateEnvelope was for different channel than envelope: %s vs %s", configUpdate.ChannelId, header.ChannelId)
	}

	fmt.Printf("\nChannel creation for channel: %s\n", header.ChannelId)
	fmt.Println()

	if configUpdate.ReadSet == nil {
		fmt.Println("Read Set: empty")
	} else {
		fmt.Println("Read Set:")
		readSetAsJSON, err := configGroupAsJSON(configUpdate.ReadSet)
		if err != nil {
			return err
		}
		fmt.Println(readSetAsJSON)
	}
	fmt.Println()

	if configUpdate.WriteSet == nil {
		return fmt.Errorf("Empty WriteSet")
	}

	fmt.Println("Write Set:")
	writeSetAsJSON, err := configGroupAsJSON(configUpdate.WriteSet)
	if err != nil {
		return err
	}
	fmt.Println(writeSetAsJSON)
	fmt.Println()

	readSetMap, err := MapConfig(configUpdate.ReadSet) //SOURCE:configtx.MapConfig
	if err != nil {
		return fmt.Errorf("Error mapping read set: %s", err)
	}
	writeSetMap, err := MapConfig(configUpdate.WriteSet) //SOURCE:configtx.MapConfig
	if err != nil {
		return fmt.Errorf("Error mapping write set: %s", err)
	}

	fmt.Println("Delta Set:")
	deltaSet := ComputeDeltaSet(readSetMap, writeSetMap) //SOURCE:configtx.ComputeDeltaSet
	for key := range deltaSet {
		fmt.Println(key)
	}
	fmt.Println()

	return nil
}

func main() {
	var outputBlock, outputChannelCreateTx, profile, channelID, inspectBlock, inspectChannelCreateTx, outputAnchorPeersUpdate, asOrg string

	flag.StringVar(&outputBlock, "outputBlock", "", "The path to write the genesis block to (if set)")
	flag.StringVar(&channelID, "channelID", TestChainID, "The channel ID to use in the configtx") //SOURCE:provisional.TestChainID
	flag.StringVar(&outputChannelCreateTx, "outputCreateChannelTx", "", "The path to write a channel creation configtx to (if set)")
	flag.StringVar(&profile, "profile", SampleInsecureProfile, "The profile from configtx.yaml to use for generation.") //SOURCE:genesisconfig.SampleInsecureProfile
	flag.StringVar(&inspectBlock, "inspectBlock", "", "Prints the configuration contained in the block at the specified path")
	flag.StringVar(&inspectChannelCreateTx, "inspectChannelCreateTx", "", "Prints the configuration contained in the transaction at the specified path")
	flag.StringVar(&outputAnchorPeersUpdate, "outputAnchorPeersUpdate", "", "Creates an config update to update an anchor peer (works only with the default channel creation, and only for the first update)")
	flag.StringVar(&asOrg, "asOrg", "", "Performs the config generation as a particular organization (by name), only including values in the write set that org (likely) has privilege to set")

	version := flag.Bool("version", false, "Show version information")

	flag.Parse()

	// show version
	if *version {
		printVersion()
		os.Exit(exitCode)
	}

	logging.SetLevel(logging.INFO, "")

	// don't need to panic when running via command line
	defer func() {
		if err := recover(); err != nil {
			if strings.Contains(fmt.Sprint(err), "Error reading configuration: Unsupported Config Type") {
				logger.Error("Could not find configtx.yaml. " +
					"Please make sure that FABRIC_CFG_PATH is set to a path " +
					"which contains configtx.yaml")
			}
			os.Exit(1)
		}
	}()

	logger.Info("Loading configuration")
	InitFactories(nil) //SOURCE:factory.InitFactories
	config := ConfigLoad(profile) //SOURCE:genesisconfig.Load //DEFAULT:SampleInsecureProfile="SampleInsecureSolo"

	if outputBlock != "" {
		if err := doOutputBlock(config, channelID, outputBlock); err != nil {
			logger.Fatalf("Error on outputBlock: %s", err)
		}
	}

	if outputChannelCreateTx != "" {
		if err := doOutputChannelCreateTx(config, channelID, outputChannelCreateTx); err != nil {
			logger.Fatalf("Error on outputChannelCreateTx: %s", err)
		}
	}

	if inspectBlock != "" {
		if err := doInspectBlock(inspectBlock); err != nil {
			logger.Fatalf("Error on inspectBlock: %s", err)
		}
	}

	if inspectChannelCreateTx != "" {
		if err := doInspectChannelCreateTx(inspectChannelCreateTx); err != nil {
			logger.Fatalf("Error on inspectChannelCreateTx: %s", err)
		}
	}

	if outputAnchorPeersUpdate != "" {
		if err := doOutputAnchorPeersUpdate(config, channelID, outputAnchorPeersUpdate, asOrg); err != nil {
			logger.Fatalf("Error on inspectChannelCreateTx: %s", err)
		}
	}
}

func printVersion() {
	fmt.Println(GetVersionInfo())
}
