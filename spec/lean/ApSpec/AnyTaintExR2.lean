/-
  ApSpec.AnyTaintExR2 — the cleaner `part` row with rule R2 (ap.md §4.7 "R2",
  spec/acyclic-group-a-implementation.md §4, landed in commit `5804e44dd`).

  R2: an `exact` cleaner does not apply to a normal `[any-taint]/E` fact (`carriesB`). The fact stays
  as it is: the same layer, mark and exclusion. The earlier row `partX` (AnyTaintExDefs) sends it to
  the demand layer through the base `concPart` and drops `E`.

  This module states the R2 row and relates it to `partX` (the proposal's C1-C4 at the ApSpec level).
  The closure, coverage and exactness theorems of the `AnyTaintEx*` modules are stated on `partX`, so
  they describe the deleted row; they are not re-proved for R2 here.
-/
import ApSpec.AnyTaintExDefs

namespace ApSpec.AnyTaintEx
open ApSpec ApSpec.AnyTaint

/-- The scope of R2: a normal `[any-taint]` fact with a concrete mark, under an `exact` cleaner. -/
def inR2 (cl : Cleaner) (c : XFact) : Bool := carriesB c.af && cl.reach == .exact

/-- The `part` result of a cleaned concrete mark with R2. -/
def partXR2 (cl : Cleaner) (c : XFact) : List XFact := if inR2 cl c then [c] else partX cl c

/-- The refined cleaner with R2: `cleanResX` with `partXR2` in the `part` row of a cleaned concrete
    mark. Every other row is the row of `cleanResX`. -/
def cleanResXR2 (cl : Cleaner) (c : XFact) : ResX :=
  match cleanPosX cl c, c.af.fact.mark with
  | .part, .conc t => if cl.markB t then ⟨partXR2 cl c, []⟩ else ⟨[c], []⟩
  | _,     _       => cleanResX cl c

/-- C2: in scope, R2 gives the input fact. -/
theorem partXR2_keeps {cl : Cleaner} {c : XFact} (h : inR2 cl c = true) : partXR2 cl c = [c] := by
  simp [partXR2, h]

/-- C3: outside the scope, R2 is the earlier row. -/
theorem partXR2_outside {cl : Cleaner} {c : XFact} (h : inR2 cl c = false) :
    partXR2 cl c = partX cl c := by
  simp [partXR2, h]

/-- The earlier row under an `exact` cleaner is the base `concPart` with the exclusion dropped. -/
theorem partX_exact {cl : Cleaner} {c : XFact} (h : cl.reach = .exact) :
    partX cl c = [⟨concPart cl c.af, Excl.empty⟩] := by
  unfold partX
  cases carriesB c.af <;> simp [h]

/-- Under an `exact` cleaner the base `concPart` keeps the fact and sets the demand layer. -/
theorem concPart_exact {cl : Cleaner} {a : AFact} (h : cl.reach = .exact) :
    concPart cl a = ⟨a.fact, true⟩ := by
  unfold concPart
  split
  · rename_i hr _
    rw [h] at hr
    cases hr
  · rfl

/-- C1 and C4: in scope, the earlier row is the R2 result moved to the demand layer, with the
    exclusion dropped (production keeps `E` on that row; spec/acyclic-group-a-implementation.md §4.4). -/
theorem partX_is_r2_on_demand {cl : Cleaner} {c : XFact} (h : inR2 cl c = true) :
    partX cl c = [⟨⟨c.af.fact, true⟩, Excl.empty⟩] ∧ partXR2 cl c = [c] := by
  have hr : cl.reach = .exact := by
    simp [inR2] at h
    exact h.2
  refine ⟨?_, partXR2_keeps h⟩
  rw [partX_exact hr, concPart_exact hr]

/-- C6: in scope, R2 keeps the layer (the normal layer, since `carriesB`). -/
theorem partXR2_normal {cl : Cleaner} {c : XFact} (h : inR2 cl c = true) :
    ∀ r ∈ partXR2 cl c, r.af.demand = false := by
  have hc : carriesB c.af = true := by
    simp [inR2] at h
    exact h.1
  intro r hrm
  rw [partXR2_keeps h] at hrm
  simp at hrm
  subst hrm
  cases hd : r.af.demand
  · rfl
  · simp [carriesB, hd] at hc

/-- C8: the whole refined cleaner changes only in scope. -/
theorem cleanResXR2_outside {cl : Cleaner} {c : XFact} (h : inR2 cl c = false) :
    cleanResXR2 cl c = cleanResX cl c := by
  unfold cleanResXR2
  split
  · rename_i t hp hm
    unfold cleanResX
    rw [hp, hm]
    simp [partXR2_outside h]
  · rfl

end ApSpec.AnyTaintEx
