import Std

/-!
Exact coordinates, not AP coverage. A coordinate includes the full field path,
EXACT/ANY leaf kind, and mark. Finite Bool arrays are executable. Header
canonicalization is the same supplied function in both constructors.
-/
namespace ProtectionAdmission

abbrev Root (n : Nat) := Fin n → Bool
def included (p r : Root n) : Prop := ∀ c, p c = true → r c = true
def union (a b : Root n) : Root n := fun c => a c || b c
def trim (p r : Root n) : Root n := fun c => p c && r c

theorem trim_subset (p r : Root n) : included (trim p r) r := by
  intro c h
  exact (Bool.and_eq_true_iff.mp h).2

theorem trim_identity (p r : Root n) (h : included p r) : trim p r = p := by
  funext c
  cases hp : p c with
  | false => simp [trim, hp]
  | true => simp [trim, hp, h c hp]

theorem union_included (p q a b : Root n) (pa : included p a)
    (qb : included q b) : included (union p q) (union a b) := by
  intro c h
  rcases Bool.or_eq_true_iff.mp h with hp | hq
  · simp [union, pa c hp]
  · simp [union, qb c hq]

theorem right_in_union (a p : Root n) : included p (union a p) := by
  intro c h; simp [union, h]

theorem coordinate_restriction (p r keep : Root n) (h : included p r) :
    included (trim p keep) (trim r keep) := by
  intro c hc
  obtain ⟨hp, hk⟩ := Bool.and_eq_true_iff.mp hc
  simp [trim, h c hp, hk]

theorem equivalent_root_preserves (p r replacement : Root n)
    (same : ∀ c, replacement c = r c) (h : included p r) : included p replacement := by
  intro c hp; rw [same]; exact h c hp

structure Tree (Header : Type) (n : Nat) where
  header : Header
  ordinary : Root n
  mask : Root n

def legacy {H : Type} (canonical : H → Root n → H)
    (header : H) (r p : Root n) : Tree H n :=
  ⟨canonical header r, r, trim p r⟩

def certified {H : Type} (canonical : H → Root n → H)
    (header : H) (r p : Root n) : Tree H n :=
  ⟨canonical header r, r, p⟩

theorem constructor_exact {H : Type} (canonical : H → Root n → H)
    (header : H) (r p : Root n) (h : included p r) :
    legacy canonical header r p = certified canonical header r p := by
  simp only [legacy, certified, trim_identity p r h]

/-- withRoot's old mask is discarded by the following withProtection call. -/
def legacyChain {H : Type} (canonical : H → Root n → H)
    (header : H) (r oldP newP : Root n) : Tree H n :=
  let intermediate := legacy canonical header r oldP
  ⟨intermediate.header, intermediate.ordinary, trim newP intermediate.ordinary⟩

theorem discarded_intermediate {H : Type} (canonical : H → Root n → H)
    (header : H) (r oldP newP : Root n) :
    legacyChain canonical header r oldP newP = legacy canonical header r newP := rfl

theorem stored_union_exact {H : Type} (canonical : H → Root n → H)
    (header : H) (a b p q : Root n) (pa : included p a) (qb : included q b) :
    legacyChain canonical header (union a b) p (union p q) =
      certified canonical header (union a b) (union p q) := by
  rw [discarded_intermediate]
  exact constructor_exact _ _ _ _ (union_included p q a b pa qb)

/-- TaintGroup explicitly unions the whole remainder mask into its delta root. -/
theorem taint_group_delta_exact {H : Type} (canonical : H → Root n → H)
    (header : H) (ordinaryDelta remainderMask : Root n) :
    legacy canonical header (union ordinaryDelta remainderMask) remainderMask =
      certified canonical header (union ordinaryDelta remainderMask) remainderMask :=
  constructor_exact _ _ _ _ (right_in_union ordinaryDelta remainderMask)

/-- The two subtraction procedures are unchanged; only final construction changes. -/
theorem subtraction_result_exact {H : Type} (canonical : H → Root n → H)
    (header : H) (ordinaryRest protectedRest oldMask : Root n) :
    legacyChain canonical header (union ordinaryRest protectedRest) oldMask protectedRest =
      certified canonical header (union ordinaryRest protectedRest) protectedRest := by
  rw [discarded_intermediate]
  exact constructor_exact _ _ _ _ (right_in_union ordinaryRest protectedRest)

theorem exclusion_only_exact {H : Type} (canonical : H → Root n → H)
    (newHeader : H) (r p q : Root n) (pr : included p r) (qr : included q r) :
    legacy canonical newHeader r (union p q) =
      certified canonical newHeader r (union p q) := by
  apply constructor_exact
  intro c h
  rcases Bool.or_eq_true_iff.mp h with hp | hq
  · exact pr c hp
  · exact qr c hq

theorem interned_result_exact {H : Type} (canonical : H → Root n → H)
    (header : H) (r replacement p : Root n) (same : ∀ c, replacement c = r c)
    (pr : included p r) :
    legacy canonical header replacement p = certified canonical header replacement p :=
  constructor_exact _ _ _ _ (equivalent_root_preserves p r replacement same pr)

theorem unchanged_header {H : Type} (canonical : H → Root n → H)
    (header : H) (r p : Root n) :
    (legacy canonical header r p).header = (certified canonical header r p).header := rfl

/-- There is no semantic weakening of protection in any certified constructor. -/
theorem protection_exact {H : Type} (canonical : H → Root n → H)
    (header : H) (r p : Root n) (pr : included p r) (c : Fin n) :
    (legacy canonical header r p).mask c = p c := by
  simp [legacy, trim_identity p r pr]

def a : Root 2 := fun c => c == 0
def b : Root 2 := fun c => c == 1

/-- A certificate for the merged root cannot be reused for an arbitrary delta. -/
theorem merged_mask_not_delta : ¬ included a b := by
  intro h
  have impossible := h 0 (by decide)
  contradiction

theorem merged_mask_valid : included a (union a b) := by
  intro c h; simp [union, h]

theorem same_ordinary_different_protection :
    (certified (fun h _ => h) () (union a b) a).ordinary =
      (certified (fun h _ => h) () (union a b) b).ordinary ∧
    (certified (fun h _ => h) () (union a b) a).mask 0 ≠
      (certified (fun h _ => h) () (union a b) b).mask 0 := by
  exact ⟨rfl, by decide⟩

example : (trim a b) 0 = false := by decide
example : (union a b) 0 = true ∧ (union a b) 1 = true := by decide

end ProtectionAdmission
