package sarif

import (
	"fmt"
	"strings"
)

// Suppression semantics, per SARIF §3.35 and the read rule in the design:
//
//   - status absent or "accepted" — suppressed. "accepted" is what triage
//     --accept writes: the team will not fix this.
//   - "underReview" — suppressed, and reported separately as deferred. This is
//     what triage --defer writes: the team is not fixing it for now.
//   - "rejected" — not suppressed. The suppression was explicitly denied, so
//     reporting the finding is the whole point.
//   - anything else — not suppressed, and counted so the report says so.
//
// Nothing but SARIF's own fields is written: kind, status, justification, guid.

// honors reports whether a single suppression entry hides its result.
func honors(s *Suppression) bool {
	if s.Status == nil {
		return true
	}
	switch *s.Status {
	case Accepted, UnderReview:
		return true
	default:
		return false
	}
}

// IsSuppressed reports whether any suppression on the result is honored.
func IsSuppressed(r *Result) bool {
	return honoredSuppression(r) != nil
}

// honoredSuppression returns the first suppression entry that hides the result,
// or nil when none does.
func honoredSuppression(r *Result) *Suppression {
	if r == nil {
		return nil
	}
	for i := range r.Suppressions {
		if honors(&r.Suppressions[i]) {
			return &r.Suppressions[i]
		}
	}
	return nil
}

// IsDeferred reports whether the honored suppression is a deferral
// ("not fixing for now") rather than an acceptance ("won't fix").
func IsDeferred(r *Result) bool {
	s := honoredSuppression(r)
	return s != nil && s.Status != nil && *s.Status == UnderReview
}

// JustificationOf returns the justification of the honored suppression, or ""
// when the result is not suppressed or the entry carries no justification.
func JustificationOf(r *Result) string {
	s := honoredSuppression(r)
	if s == nil || s.Justification == nil {
		return ""
	}
	return *s.Justification
}

// StatusOf returns the honored suppression's status as a string, defaulting to
// "accepted" when the entry omits it (which is how the read rule treats it).
func StatusOf(r *Result) string {
	s := honoredSuppression(r)
	if s == nil {
		return ""
	}
	if s.Status == nil {
		return string(Accepted)
	}
	return string(*s.Status)
}

// Accept records that the team will not fix this finding, writing an external
// suppression with status "accepted". Any suppression already on the result is
// replaced: a result carries one decision, the most recent one.
func Accept(r *Result, justification string) error {
	return suppress(r, Accepted, justification)
}

// Defer records that the team is not fixing this finding for now, writing an
// external suppression with status "underReview".
func Defer(r *Result, justification string) error {
	return suppress(r, UnderReview, justification)
}

func suppress(r *Result, status Status, justification string) error {
	justification = strings.TrimSpace(justification)
	if justification == "" {
		return fmt.Errorf("a justification is required to suppress a finding")
	}
	guid := newUUIDv4()
	statusValue := status
	r.Suppressions = []Suppression{{
		Kind:          External,
		Status:        &statusValue,
		Justification: &justification,
		GUID:          &guid,
	}}
	return nil
}

// Unsuppress removes every suppression from the result, reporting whether
// anything was removed. It only affects the report being triaged: if a baseline
// still carries the decision, the next scan inherits it again.
func Unsuppress(r *Result) bool {
	if len(r.Suppressions) == 0 {
		return false
	}
	r.Suppressions = nil
	return true
}

// InheritSuppressions copies honored suppressions from baseline results onto
// matching current results, and returns how many were copied. The copy is
// verbatim — same status, justification and guid — so a decision authored once
// stays attached to the finding across every later scan.
//
// Presence in the baseline is not acceptance: a baseline result without a
// suppression transmits nothing. A result that already carries its own
// suppression is left alone. Its own decision is the newer one.
func InheritSuppressions(current, baseline *Report, key string) int {
	byIdentity := make(map[string]*Suppression)
	for _, r := range baseline.Results() {
		id, ok := Identity(r, key)
		if !ok {
			continue
		}
		if _, seen := byIdentity[id]; seen {
			continue
		}
		if s := honoredSuppression(r); s != nil {
			byIdentity[id] = s
		}
	}

	inherited := 0
	for _, r := range current.Results() {
		if len(r.Suppressions) > 0 {
			continue
		}
		id, ok := Identity(r, key)
		if !ok {
			continue
		}
		source, found := byIdentity[id]
		if !found {
			continue
		}
		r.Suppressions = []Suppression{copySuppression(source)}
		inherited++
	}
	return inherited
}

// copySuppression deep-copies the parts of a suppression we carry forward.
// Pointers are cloned so the two reports never share mutable state.
func copySuppression(s *Suppression) Suppression {
	out := Suppression{Kind: s.Kind, Location: s.Location, Properties: s.Properties}
	if s.Status != nil {
		status := *s.Status
		out.Status = &status
	}
	if s.Justification != nil {
		justification := *s.Justification
		out.Justification = &justification
	}
	if s.GUID != nil {
		guid := *s.GUID
		out.GUID = &guid
	}
	return out
}

// SuppressionStats summarizes the suppression state of a report.
type SuppressionStats struct {
	Total      int // all results
	Suppressed int // results hidden by an honored suppression
	WontFix    int // honored, status accepted (or absent)
	Deferred   int // honored, status underReview
	NotHonored int // results carrying only rejected or unrecognised suppressions
}

// Any reports whether the report contains any suppression at all, honored or
// not — the signal for whether to render the Suppressions summary group.
func (s SuppressionStats) Any() bool {
	return s.Suppressed > 0 || s.NotHonored > 0
}

// CollectSuppressionStats walks the report and counts suppression states.
func CollectSuppressionStats(report *Report) SuppressionStats {
	var stats SuppressionStats
	for _, r := range report.Results() {
		stats.Total++
		switch {
		case IsSuppressed(r):
			stats.Suppressed++
			if IsDeferred(r) {
				stats.Deferred++
			} else {
				stats.WontFix++
			}
		case len(r.Suppressions) > 0:
			stats.NotHonored++
		}
	}
	return stats
}
