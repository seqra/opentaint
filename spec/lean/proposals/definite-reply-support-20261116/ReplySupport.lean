import UniformCycle

/- The support quotient is parametric in eligibility. DefiniteSupport selects
   only actual FULL exact and uniform replies, with complete literal keys. -/
namespace ReplySupportKernel
open ExactSupport

def absorb (eligible : Key → Bool) (packet : List Item) : List Item :=
  packet.filter fun x => !x.demand || !eligible x.key || !decide (normal x ∈ packet)

variable (eligible : Key → Bool)

theorem membership (xs : List Item) (x : Item) :
    x ∈ absorb eligible xs ↔ x ∈ xs ∧
      (x.demand = false ∨ eligible x.key = false ∨ normal x ∉ xs) := by
  simp [absorb,Bool.or_eq_true,or_assoc]

theorem subset (xs : List Item) (x : Item) (hx : x ∈ absorb eligible xs) : x ∈ xs :=
  ((membership eligible xs x).mp hx).1

theorem all_normal_members_retained (xs : List Item) (x : Item)
    (hx : x ∈ xs) (hn : x.demand = false) : x ∈ absorb eligible xs := by
  exact (membership eligible xs x).mpr ⟨hx,Or.inl hn⟩

theorem normal_members_unchanged (xs : List Item) (x : Item) (hn : x.demand = false) :
    x ∈ absorb eligible xs ↔ x ∈ xs :=
  ⟨subset eligible xs x, fun hx => all_normal_members_retained eligible xs x hx hn⟩

theorem missing_normal_keeps_demand (xs : List Item) (x : Item)
    (hx : x ∈ xs) (missing : normal x ∉ xs) : x ∈ absorb eligible xs :=
  (membership eligible xs x).mpr ⟨hx,Or.inr (Or.inr missing)⟩

theorem unsupported_members_retained (xs : List Item) (x : Item)
    (hx : x ∈ xs) (unsupported : eligible x.key = false) : x ∈ absorb eligible xs :=
  (membership eligible xs x).mpr ⟨hx,Or.inr (Or.inl unsupported)⟩

/-- The deleted member has an explicit retained NORMAL witness, with every
    scope, premise, mark, field, protection and resume coordinate unchanged. -/
theorem deletion_has_retained_witness (xs : List Item) (x : Item)
    (hx : x ∈ xs) (gone : x ∉ absorb eligible xs) :
    x.demand = true ∧ eligible x.key = true ∧ normal x ∈ absorb eligible xs := by
  have hd : x.demand = true := by
    cases h : x.demand
    · exact False.elim (gone (all_normal_members_retained eligible xs x hx h))
    · rfl
  have he : eligible x.key = true := by
    cases h : eligible x.key
    · exact False.elim (gone (unsupported_members_retained eligible xs x hx h))
    · rfl
  have hm : normal x ∈ xs := by
    by_cases h : normal x ∈ xs
    · exact h
    · exact False.elim (gone (missing_normal_keeps_demand eligible xs x hx h))
  exact ⟨hd,he,all_normal_members_retained eligible xs (normal x) hm rfl⟩

theorem same_observable_keys (xs : List Item) (k : Key) :
    (∃ x ∈ xs, x.key = k) ↔ ∃ x ∈ absorb eligible xs, x.key = k := by
  constructor
  · rintro ⟨x,hx,hk⟩
    by_cases h : x ∈ absorb eligible xs
    · exact ⟨x,h,hk⟩
    · exact ⟨normal x,(deletion_has_retained_witness eligible xs x hx h).2.2,hk⟩
  · rintro ⟨x,hx,hk⟩; exact ⟨x,subset eligible xs x hx,hk⟩

theorem idempotent_membership (xs : List Item) (x : Item) :
    x ∈ absorb eligible (absorb eligible xs) ↔ x ∈ absorb eligible xs := by
  constructor
  · exact subset eligible (absorb eligible xs) x
  · intro hx
    apply (membership eligible (absorb eligible xs) x).mpr
    refine ⟨hx,?_⟩
    rcases ((membership eligible xs x).mp hx).2 with hn | he | hm
    · exact Or.inl hn
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (fun h => hm (subset eligible xs (normal x) h)))

theorem order_independent (xs ys : List Item)
    (same : ∀ x, x ∈ xs ↔ x ∈ ys) (x : Item) :
    x ∈ absorb eligible xs ↔ x ∈ absorb eligible ys := by
  simp only [membership,same]

theorem merge_membership (xs ys : List Item) (x : Item) :
    x ∈ absorb eligible (absorb eligible xs ++ ys) ↔ x ∈ absorb eligible (xs ++ ys) := by
  have hn := normal_members_unchanged eligible xs (normal x) rfl
  rw [membership,membership]
  simp only [List.mem_append]
  constructor
  · rintro ⟨hx,hfilter⟩
    refine ⟨hx.elim (fun h => Or.inl (subset eligible xs x h)) Or.inr,?_⟩
    simpa only [hn] using hfilter
  · rintro ⟨hx,hfilter⟩
    refine ⟨?_,?_⟩
    · rcases hx with hx | hx
      · left
        apply (membership eligible xs x).mpr
        refine ⟨hx,?_⟩
        rcases hfilter with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (fun hm => h (Or.inl hm)))
      · exact Or.inr hx
    · simpa only [hn] using hfilter


end ReplySupportKernel
