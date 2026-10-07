/-
  ApSpec.PipelineStore — the index lookups of the storage with subscription (analyzer-core.md §5.3).

  The callee keys its publications by `keyB` of the premise (`base :: path`); the caller keys its
  subscriptions by `keyB` of the added fact. The replay looks up the publications for a new added
  fact `a`; the delivery looks up the subscriptions for a new premise `j`. Each lookup returns
  every entry that the exact test accepts:

  | test                        | replay (publications for `a`)  | delivery (subscriptions for `j`) |
  |-----------------------------|--------------------------------|----------------------------------|
  | run 1, `applicable j a`     | `lookupPrefixes (keyB a)`      | `lookupExtensions (keyB j)`      |
  | restricted, `satI j a`      | `lookupExtensions (keyB a)`    | `lookupPrefixes (keyB j)`        |
  | a record, `satI ∨ applicable` | `around (keyB a)`            | (records are read-only)          |

  Theorems: `replay_run1`, `deliver_run1`, `replay_restricted`, `deliver_restricted`,
  `record_lookup`. The match test after the lookup is the one test `matches` of §5.3 (P4).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.Store
import ApSpec.Restricted

namespace ApSpec.PipelineStore
open ApSpec ApSpec.Store

variable {ρ : Type}

/-- `satI j a`: `a` and `j` have the same base, and the path of `j` extends the path of `a`. -/
theorem satI_parts {j a : PFact} (h : satI j a = true) :
    a.base = j.base ∧ ∃ r, j.path = a.path ++ r := by
  unfold satI at h
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  have h2 := coversB_parts (i := ⟨a.base, a.path, a.kind, .star⟩) h1
  exact h2

/-- Run 1, the replay: a publication whose premise `prem p` is applicable to the added fact `a`
    is on the key path of `a`. -/
theorem replay_run1 {prem : ρ → PFact} {pubs : List ρ} {a : PFact} {p : ρ}
    (hp : p ∈ pubs) (h : applicable (prem p) a = true) :
    p ∈ (indexBy (fun x => keyB (prem x)) pubs).lookupPrefixes (keyB a) := by
  have ⟨hb, r, hr⟩ := applicable_parts h
  refine mem_prefixes_indexBy.mpr ⟨hp, r, ?_⟩
  simp only [keyB, hb, hr, List.cons_append]

#print axioms replay_run1

/-- Run 1, the delivery: a subscription whose added fact `fact s` the premise `j` is applicable
    to is below the key path of `j`. -/
theorem deliver_run1 {fact : ρ → PFact} {subs : List ρ} {j : PFact} {s : ρ}
    (hs : s ∈ subs) (h : applicable j (fact s) = true) :
    s ∈ (indexBy (fun x => keyB (fact x)) subs).lookupExtensions (keyB j) := by
  have ⟨hb, r, hr⟩ := applicable_parts h
  refine mem_extensions_indexBy.mpr ⟨hs, r, ?_⟩
  simp only [keyB, hb, hr, List.cons_append]

#print axioms deliver_run1

/-- A restricted run, the replay: a publication whose premise lies inside the added fact `a` is
    below the key path of `a`. -/
theorem replay_restricted {prem : ρ → PFact} {pubs : List ρ} {a : PFact} {p : ρ}
    (hp : p ∈ pubs) (h : satI (prem p) a = true) :
    p ∈ (indexBy (fun x => keyB (prem x)) pubs).lookupExtensions (keyB a) := by
  have ⟨hb, r, hr⟩ := satI_parts h
  refine mem_extensions_indexBy.mpr ⟨hp, r, ?_⟩
  simp only [keyB, hb, hr, List.cons_append]

#print axioms replay_restricted

/-- A restricted run, the delivery: a subscription whose added fact contains the premise `j` is
    on the key path of `j`. -/
theorem deliver_restricted {fact : ρ → PFact} {subs : List ρ} {j : PFact} {s : ρ}
    (hs : s ∈ subs) (h : satI j (fact s) = true) :
    s ∈ (indexBy (fun x => keyB (fact x)) subs).lookupPrefixes (keyB j) := by
  have ⟨hb, r, hr⟩ := satI_parts h
  refine mem_prefixes_indexBy.mpr ⟨hs, r, ?_⟩
  simp only [keyB, hb, hr, List.cons_append]

#print axioms deliver_restricted

/-- A record applies by `satI` or by `applicable` (`DR.retRec`): it is on the key path of the
    added fact or below it, so the lookup `around` returns it. -/
theorem record_lookup {prem : ρ → PFact} {recs : List ρ} {a : PFact} {x : ρ}
    (hx : x ∈ recs) (h : satI (prem x) a = true ∨ applicable (prem x) a = true) :
    x ∈ around (indexBy (fun y => keyB (prem y)) recs) (keyB a) := by
  refine mem_around_indexBy.mpr ⟨hx, ?_⟩
  cases h with
  | inl h =>
    have ⟨hb, r, hr⟩ := satI_parts h
    exact Or.inr ⟨r, by simp only [keyB, hb, hr, List.cons_append]⟩
  | inr h =>
    have ⟨hb, r, hr⟩ := applicable_parts h
    exact Or.inl ⟨r, by simp only [keyB, hb, hr, List.cons_append]⟩

#print axioms record_lookup

end ApSpec.PipelineStore
