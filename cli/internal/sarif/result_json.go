package sarif

import "encoding/json"

// MarshalJSON preserves the distinction SARIF assigns to suppressions: nil
// means suppression information is unavailable, while an empty array means it
// was evaluated and the result is not suppressed. The generated struct uses
// omitempty, which otherwise collapses those two states.
func (r Result) MarshalJSON() ([]byte, error) {
	type resultAlias Result
	if r.Suppressions == nil {
		return json.Marshal(resultAlias(r))
	}
	return json.Marshal(struct {
		resultAlias
		Suppressions []Suppression `json:"suppressions"`
	}{
		resultAlias:  resultAlias(r),
		Suppressions: r.Suppressions,
	})
}
