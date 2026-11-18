import AuditKernel
import BoundCoreProof
import UniformSafety
import HeadSafety
namespace AuditGeometry
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def pointAt (path : Path) (suffix : Path) := path++suffix

theorem MAY_is_empty_or_nonempty_without_a_named_first_field (suffix : Path) :
    suffix=[] ∨ ∃ f rest,suffix=f::rest := by
  cases suffix with
  | nil => exact Or.inl rfl
  | cons f rest => exact Or.inr ⟨f,rest,rfl⟩

theorem every_real_cut_keeps_its_original_point
    (base : Ap) (kept : Path) (field : Nat) (lost suffix : Path) :
    UniformActual.locationIn {base with path:=kept,tail:=.ne,e:=[]}
      (kept++(field::lost)++suffix) := by
  refine ⟨(field::lost)++suffix,by simp [List.append_assoc],?_⟩
  simp [admits]

theorem an_uncut_empty_suffix_cannot_be_relabelled_nonempty :
    ¬UniformActual.locationIn (⟨0,[],.ne,some 1,[],[]⟩ : Ap) [] := by
  rintro ⟨rest,located,allowed⟩
  simp only [List.nil_append] at located
  subst rest
  simp [admits] at allowed

theorem unknown_read_of_NE_must_allow_an_empty_residual (field : Nat) (rest : Path) :
    dropHead [field] (field::rest)=some rest ∧ admits .may [] rest=true := by
  cases rest <;> simp [dropHead,admits]

theorem known_read_preserves_the_nonempty_remainder
    (known : Path) (field : Nat) (rest : Path) :
    ∃ suffix,known++(field::rest)=known++suffix ∧ suffix≠[] := by
  exact ⟨field::rest,rfl,by simp⟩

theorem a_written_MAY_retains_every_possible_written_location
    (base : Ap) (write source : Path) :
    UniformActual.locationIn {base with path:=write,tail:=.may,e:=[]} (write++source) := by
  exact ⟨source,rfl,by cases source <;> simp [admits]⟩

theorem an_unknown_written_value_can_be_the_written_field_itself (field : Nat) :
    UniformActual.locationIn (⟨0,[field],.may,some 1,[],[]⟩ : Ap) [field] ∧
    ¬UniformActual.locationIn (⟨0,[field],.ne,some 1,[],[]⟩ : Ap) [field] := by
  constructor
  · exact ⟨[],by simp,rfl⟩
  · rintro ⟨rest,located,allowed⟩
    have empty : rest=[] := by simpa using located.symm
    subst rest
    simp [admits] at allowed

-- No continuation-monotonicity premise remains for finite positive Horn
-- programs. They include complete AND premises and arbitrary finite paths.
theorem uniform_actual_cover_preserves_the_entire_positive_program
    (normal candidate : ExactSupport.Item)
    (covered : UniformActual.covers normal candidate=true)
    (program : List (AuditKernel.Rule UniformSafety.Point))
    (observation : UniformSafety.Point)
    (old : AuditKernel.Derives program (UniformSafety.supports candidate) observation) :
    AuditKernel.Derives program (UniformSafety.supports normal) observation := by
  apply AuditKernel.positive_ND_closure_preserves_every_derivation program
    (UniformSafety.supports candidate) (UniformSafety.supports normal) _ observation old
  intro point present
  exact AuditKernel.Derives.initial point
    (UniformSafety.every_possible_point_has_the_retained_definite_support normal candidate covered point present)

theorem unchanged_head_real_E_copy_loses_no_actual_point
    (actual : Offered) (query : Seed) (eligible : CarryPolicy.eligible actual query=true)
    (point : Path) :
    UniformActual.locationIn (CarryPolicy.carry actual query).ap point ↔
    UniformActual.locationIn actual.ap point :=
  CarrySafety.eligible_copy_preserves_the_entire_actual_point_region actual query eligible point

theorem retained_MUST_head_and_real_E_lose_no_actual_point
    (actual : Offered) (query : Seed) (eligible : HeadPolicy.eligible actual query=true)
    (point : Path) :
    UniformActual.locationIn (HeadPolicy.retain actual query).ap point ↔
    UniformActual.locationIn actual.ap point :=
  HeadSafety.retains_the_actual_point_region actual query eligible point

theorem retaining_a_real_hole_does_not_claim_uniform_support_for_STAR
    (actual : Offered) (query : Seed) :
    (HeadPolicy.retain actual query).ap.tail=query.ap.tail ∧
    (HeadPolicy.retain actual query).demand=query.demand :=
  ⟨(HeadSafety.preserves_kind_mark_support actual query).2.1,
    (HeadSafety.preserves_kind_mark_support actual query).2.2.2.2⟩

end AuditGeometry
