package sarif

import (
	"bytes"
	"encoding/json"
	"sort"
)

// UnmarshalJSON decodes a property bag, lifting "tags" into the typed field and
// keeping every other key as raw JSON in Extra. Raw JSON rather than any:
// re-encoding through map[string]any would reformat numbers and can lose
// precision on integers beyond float64's exact range.
func (p *PropertyBag) UnmarshalJSON(data []byte) error {
	var raw map[string]json.RawMessage
	if err := json.Unmarshal(data, &raw); err != nil {
		return err
	}

	p.Tags = nil
	p.Extra = nil

	for key, value := range raw {
		if key == "tags" {
			var tags []string
			if err := json.Unmarshal(value, &tags); err == nil {
				p.Tags = tags
				continue
			}
			// Not a string array: keep it verbatim rather than dropping it.
		}
		if p.Extra == nil {
			p.Extra = make(map[string]json.RawMessage, len(raw))
		}
		p.Extra[key] = value
	}
	return nil
}

// MarshalJSON re-emits the bag with its preserved keys. Keys are sorted so that
// rewriting an unchanged report produces byte-identical output.
func (p PropertyBag) MarshalJSON() ([]byte, error) {
	keys := make([]string, 0, len(p.Extra)+1)
	values := make(map[string]json.RawMessage, len(p.Extra)+1)

	for key, value := range p.Extra {
		keys = append(keys, key)
		values[key] = value
	}
	if len(p.Tags) > 0 {
		encoded, err := json.Marshal(p.Tags)
		if err != nil {
			return nil, err
		}
		if _, clash := values["tags"]; !clash {
			keys = append(keys, "tags")
		}
		values["tags"] = encoded
	}
	sort.Strings(keys)

	var buf bytes.Buffer
	buf.WriteByte('{')
	for i, key := range keys {
		if i > 0 {
			buf.WriteByte(',')
		}
		encodedKey, err := json.Marshal(key)
		if err != nil {
			return nil, err
		}
		buf.Write(encodedKey)
		buf.WriteByte(':')
		buf.Write(values[key])
	}
	buf.WriteByte('}')
	return buf.Bytes(), nil
}
