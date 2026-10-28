/- NOT SELECTED. CANDIDATE ONLY. User behavior decision is pending.
   This file proves a proposed operation. It does not authorize a change
   to the runtime or to the selected restricted-demand specification.
   Keep a satisfied shared FLOW form. For incomparable same-path STAR
   exclusions, refine its E by union. MUST inputs have the same local
   location geometry as STAR inputs under a STAR premise; that adapter
   projection needs separate implementation tests. -/
import ApSpec.AbsDefs
namespace ExcludedFlowCandidate
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.Abs
set_option autoImplicit false

theorem shared_satisfies_outside_same_star {d a : PFact} {l : Loc} (_hm : d.mark = .star)
    (outside : ¬ (d.path = a.path ∧ ∃ de ae, d.kind = .star de ∧ a.kind = .star ae))
    (hd : d.covers l) (ha : a.covers l) : satW (flowForm d) a = true := by
  obtain ⟨hbd, ⟨σ, hpd, htd⟩, _⟩ := hd
  obtain ⟨hba, ⟨τ, hpa, hta⟩, _⟩ := ha
  have hb1 : Nat.beq a.base (flowForm d).base = true := by
    show Nat.beq a.base d.base = true
    rw [← hba, ← hbd]; exact Nat.beq_refl _
  have hb2 : Nat.beq (flowForm d).base a.base = true := by
    show Nat.beq d.base a.base = true
    rw [← hba, ← hbd]; exact Nat.beq_refl _
  have hms1 : markSubB (flowForm d).mark a.mark = true := rfl
  have hpath : d.path ++ σ = a.path ++ τ := by rw [← hpd, ← hpa]
  rcases CoreAux.relate_common hpath with ⟨r, _, hq, hσ⟩ | ⟨r, _, hP, hr, hτ⟩
  · -- the added fact is at or below the pattern
    cases r with
    | nil =>
      have hq' : a.path = d.path := by rw [hq, List.append_nil]
      cases hdk : d.kind with
      | exact =>
        -- the flow form is `$` at the path of `a`: it lies inside `a`
        apply satW_of_satI
        apply satI_of_drop0 hb1 (by show dropPrefix a.path d.path = some []; rw [hq']; exact RAux.dropPrefix_self' _) _ hms1
        show tailSubB a.kind (flowK d.kind) = true
        rw [hdk]
        cases a.kind <;> rfl
      | any =>
        -- the flow form is `*` with the Empty exclusion at the path of `a`: it covers `a`
        apply satW_of_applicable rfl
        apply applicable_of_drop0 hb2 hms1 (by show dropPrefix d.path a.path = some []; rw [hq']; exact RAux.dropPrefix_self' _)
        · show tailSubB (flowK d.kind) a.kind = true
          rw [hdk]
          exact RCore.tailSubB_starEmpty a.kind
        · show (flowK d.kind).isAny = false
          exact flowK_not_any _
      | star e =>
        cases hak : a.kind with
        | exact =>
          apply satW_of_applicable rfl
          apply applicable_of_drop0 hb2 hms1 (by
            show dropPrefix d.path a.path = some []
            rw [hq']; exact RAux.dropPrefix_self' _)
          · show tailSubB (flowK d.kind) a.kind = true
            rw [hdk, hak]; rfl
          · exact flowK_not_any _
        | any =>
          apply satW_of_satI
          apply satI_of_drop0 hb1 (by
            show dropPrefix a.path d.path = some []
            rw [hq']; exact RAux.dropPrefix_self' _) _ hms1
          show tailSubB a.kind (flowK d.kind) = true
          rw [hdk, hak]; rfl
        | star ae =>
          exact False.elim (outside ⟨hq'.symm, e, ae, hdk, hak⟩)
    | cons x r' =>
      -- the added fact is strictly below the pattern: the flow form covers it
      have hadm : admitsTailB d.kind (x :: r') = true := by
        rw [hσ] at htd
        exact CoreAux.tailI_append_admits htd
      have hadm' : admitsTailB (flowK d.kind) (x :: r') = true := by
        cases hdk : d.kind with
        | exact => rw [hdk] at hadm; exact Bool.noConfusion hadm
        | any =>
          show Excl.empty.admits (x :: r') = true
          exact CoreAux.empty_admits _
        | star e => rw [hdk] at hadm; exact hadm
      apply satW_of_applicable rfl
      exact applicable_of_drop1 hb2 hms1 (CoreAux.dropPrefix_some.mpr hq) hadm' (flowK_not_any _)
  · -- the added fact is strictly above the pattern: the flow form lies inside it
    cases r with
    | nil => exact absurd rfl hr
    | cons x r' =>
      apply satW_of_satI
      apply satI_of_drop1 hb1 (CoreAux.dropPrefix_some.mpr hP) _ hms1
      rw [hτ] at hta
      exact CoreAux.tailI_append_admits hta


/-- Fallback changes only E, never the path, tail constructor or FLOW mark. -/
def refinedFlow (d a : PFact) : PFact :=
  match d.kind, a.kind with
  | .star de, .star ae =>
      if d.path = a.path then ⟨d.base, d.path, .star (de.union ae), .star⟩ else flowForm d
  | _, _ => flowForm d

/-- Keep the shared form whenever ordinary satisfaction already accepts it. -/
def chooseFlow (d a : PFact) : PFact :=
  if satW (flowForm d) a then flowForm d else refinedFlow d a

theorem same_star_union_contract {d a : PFact} {l : Loc} {de ae : Excl}
    (same : d.path = a.path) (dk : d.kind = .star de) (ak : a.kind = .star ae)
    (dm : d.mark = .star) (hd : d.covers l) (ha : a.covers l) :
    let j : PFact := ⟨d.base, d.path, .star (de.union ae), .star⟩
    j.covers l ∧ satW j a = true ∧ insideB j d = true := by
  obtain ⟨bd, ⟨ds, pd, td⟩, _⟩ := hd
  obtain ⟨ba, ⟨ass, pa, ta⟩, _⟩ := ha
  have suffix : ds = ass := by
    apply List.append_cancel_left (as := d.path)
    rw [← pd, same, ← pa]
  have admissible : (de.union ae).admits ds = true := by
    rw [ApSpec.Reverse.admits_union]
    have deAdm : de.admits ds = true := by simpa [dk, tailI] using td
    have aeAdm : ae.admits ds = true := by simpa [ak, tailI, ← suffix] using ta
    rw [deAdm, aeAdm]; rfl
  refine ⟨⟨bd, ⟨ds, pd, admissible⟩, trivial⟩, ?_, ?_⟩
  · apply satW_of_satI
    apply satI_of_drop0 (by rw [← ba, ← bd]; exact Nat.beq_refl _)
      (by show dropPrefix a.path d.path = some []; rw [same]; exact RAux.dropPrefix_self' _) _ rfl
    show tailSubB a.kind (.star (de.union ae)) = true
    rw [ak]
    exact RAux.subB_union_left' de ae
  · apply insideB_intro
    · unfold insideLocB coversB
      dsimp only
      rw [Nat.beq_refl, RAux.dropPrefix_self', dk]
      show (true && true && de.subB (de.union ae)) = true
      rw [Invariant.subB_union_right ae (subB_refl de)]; rfl
    · rw [dm]; rfl

/-- Full local C2 for arbitrary excluded STAR entry, on original Kind geometry.
    This removes PatTailB only for the new candidate, not for old emitW. -/
theorem choose_contract {d a : PFact} {l : Loc}
    (dm : d.mark = .star) (dk : ∃ de, d.kind = .star de)
    (hd : d.covers l) (ha : a.covers l) :
    (chooseFlow d a).covers l ∧ satW (chooseFlow d a) a = true ∧
      insideB (chooseFlow d a) d = true := by
  by_cases hs : satW (flowForm d) a = true
  · have chosen : chooseFlow d a = flowForm d := by simp [chooseFlow, hs]
    rw [chosen]
    exact ⟨flowForm_covers_of hd, hs, flowForm_inside dm⟩
  · have sharedFails : satW (flowForm d) a = false := by cases he : satW (flowForm d) a <;> simp_all
    obtain ⟨de, hdk⟩ := dk
    cases hak : a.kind with
    | exact =>
      have outside : ¬ (d.path = a.path ∧ ∃ de ae, d.kind = .star de ∧ a.kind = .star ae) := by
        rintro ⟨_, _, _, _, wrong⟩; rw [hak] at wrong; cases wrong
      exact False.elim (hs (shared_satisfies_outside_same_star dm outside hd ha))
    | any =>
      have outside : ¬ (d.path = a.path ∧ ∃ de ae, d.kind = .star de ∧ a.kind = .star ae) := by
        rintro ⟨_, _, _, _, wrong⟩; rw [hak] at wrong; cases wrong
      exact False.elim (hs (shared_satisfies_outside_same_star dm outside hd ha))
    | star ae =>
      by_cases same : d.path = a.path
      · simpa [chooseFlow, sharedFails, refinedFlow, hdk, hak, same] using
          same_star_union_contract same hdk hak dm hd ha
      · have outside : ¬ (d.path = a.path ∧ ∃ de ae, d.kind = .star de ∧ a.kind = .star ae) :=
          fun h => same h.1
        exact False.elim (hs (shared_satisfies_outside_same_star dm outside hd ha))

def emitCandidate (d a : PFact) : Option PFact :=
  (emitW d a).map (fun j => if d.mark = .star then chooseFlow d a else j)

theorem candidate_star_contract {d a : PFact} {l : Loc}
    (dm : d.mark = .star) (hd : d.covers l) (ha : a.covers l) :
    ∃ j, emitCandidate d a = some j ∧ j.covers l ∧ satW j a = true ∧
      insideB j d = true := by
  cases hk : d.kind with
  | star de =>
    obtain ⟨j0, he⟩ := RCore.emitM_complete (by rw [dm]; rfl) ha (RCore.covers_coversLoc hd)
    have emitted : emitW d a = some (flowForm d) := emitW_of_emitM_star dm he
    obtain ⟨coverage, satisfied, contained⟩ := choose_contract dm ⟨de, hk⟩ hd ha
    exact ⟨chooseFlow d a, by simp [emitCandidate, emitted, dm], coverage, satisfied, contained⟩
  | any =>
    obtain ⟨emitted, coverage, satisfied⟩ := emitW_contract_star dm (by rw [hk]; rfl) hd ha
    have chosen : chooseFlow d a = flowForm d := by simp [chooseFlow, satisfied]
    exact ⟨flowForm d, by simp [emitCandidate, emitted, dm, chosen], coverage, satisfied, flowForm_inside dm⟩
  | exact =>
    obtain ⟨emitted, coverage, satisfied⟩ := emitW_contract_star dm (by rw [hk]; rfl) hd ha
    have chosen : chooseFlow d a = flowForm d := by simp [chooseFlow, satisfied]
    exact ⟨flowForm d, by simp [emitCandidate, emitted, dm, chosen], coverage, satisfied, flowForm_inside dm⟩

/-- Concrete pattern emission remains exactly the original operation. -/
theorem concrete_unchanged {d a : PFact} (hm : d.mark ≠ .star) :
    emitCandidate d a = emitW d a := by
  simp [emitCandidate, hm]

/-- A typed abstract entry (ANY or STAR/E) produces a correlated STAR,
    never an abstract EXACT or a MUST premise. -/
theorem no_exact_flow {d a : PFact}
    (typed : d.kind = .any ∨ ∃ e, d.kind = .star e) :
    ∃ e, (chooseFlow d a).kind = .star e := by
  by_cases hs : satW (flowForm d) a = true
  · have chosen : chooseFlow d a = flowForm d := by simp [chooseFlow, hs]
    rw [chosen]
    rcases typed with any | ⟨e, star⟩
    · exact ⟨Excl.empty, by simp [flowForm, flowK, any]⟩
    · exact ⟨e, by simp [flowForm, flowK, star]⟩
  · have falseSat : satW (flowForm d) a = false := by cases he : satW (flowForm d) a <;> simp_all
    rw [chooseFlow, falseSat]
    rcases typed with any | ⟨e, star⟩
    · exact ⟨Excl.empty, by simp [refinedFlow, any, flowForm, flowK]⟩
    · cases ak : a.kind with
      | any => exact ⟨e, by simp [refinedFlow, star, ak, flowForm, flowK]⟩
      | exact => exact ⟨e, by simp [refinedFlow, star, ak, flowForm, flowK]⟩
      | star ae =>
        by_cases same : d.path = a.path
        · exact ⟨e.union ae, by simp [refinedFlow, star, ak, same]⟩
        · exact ⟨e, by simp [refinedFlow, star, ak, same, flowForm, flowK]⟩

#print axioms candidate_star_contract
#print axioms concrete_unchanged
#print axioms no_exact_flow
#print axioms shared_satisfies_outside_same_star
#print axioms same_star_union_contract
#print axioms choose_contract
end ExcludedFlowCandidate
