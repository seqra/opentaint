import Std
import Geometry

/-!
Prepared only: full scalar C5 exit meet followed by the existing counted cut.
Geometry.lean is copied byte-for-byte from the pinned 2026-11-01 model by the
root-only checker. No withdrawn SOA model is imported.

The entry image is a callback: this file does not prove new C2 completeness.
Possible output points are not a uniform MUST assertion or the complete STAR
input/output relation. The meet deliberately keeps correlated STAR whole and
keeps a FLOW candidate's slot. It is not exact set intersection. Whole FLOW
EXACT normalization and literal protected storage remain separate bridges.
-/
namespace AnnotatedC5Exit
set_option autoImplicit false

abbrev Accessor := RelativeRestriction.Accessor
abbrev Path := RelativeRestriction.Path
abbrev Tail := RelativeRestriction.Tail
abbrev Layer := RelativeRestriction.Layer
abbrev E := List Accessor

inductive Slot where
  | full (mark : Nat)
  | flow (excluded : List Nat)
  deriving DecidableEq, Repr

def slotAdmits : Slot → Nat → Prop
  | .full wanted, mark => wanted = mark
  | .flow excluded, mark => mark ∉ excluded

def slotsMeet : Slot → Slot → Bool
  | .full wanted, .full actual => decide (wanted = actual)
  | .full mark, .flow excluded | .flow excluded, .full mark => decide (mark ∉ excluded)
  | .flow _, .flow _ => true

theorem common_full_mark_passes (wanted actual : Slot) (mark : Nat)
    (left : slotAdmits wanted mark) (right : slotAdmits actual mark) :
    slotsMeet wanted actual = true := by
  cases wanted <;> cases actual <;> simp_all [slotAdmits, slotsMeet]

def admits : E → Path → Prop
  | _, [] => True
  | excluded, first :: _ => first ∉ excluded

def allows (tail : Tail) (excluded : E) (suffix : Path) : Prop :=
  match tail with
  | .exact => suffix = []
  | .may => True
  | .star | .must => admits excluded suffix

instance (excluded : E) (suffix : Path) : Decidable (admits excluded suffix) := by
  cases suffix <;> unfold admits <;> infer_instance

instance (tail : Tail) (excluded : E) (suffix : Path) : Decidable (allows tail excluded suffix) := by
  cases tail <;> unfold allows <;> infer_instance

theorem admits_empty (suffix : Path) : admits [] suffix := by
  cases suffix <;> simp [admits]

theorem admits_union (left right : E) (suffix : Path) :
    admits (left ++ right) suffix ↔ admits left suffix ∧ admits right suffix := by
  cases suffix <;> simp [admits, List.mem_append]

theorem allows_prefix (tail : Tail) (excluded : E) (left right : Path)
    (accepted : allows tail excluded (left ++ right)) : allows tail excluded left := by
  cases tail <;> cases left <;> simp_all [allows, admits]

structure Pattern where
  base : Nat
  path : Path
  tail : Tail
  slot : Slot
  exclusion : E
  deriving DecidableEq, Repr

structure Fact extends Pattern where
  layer : Layer
  h : Bool
  deriving DecidableEq, Repr

structure Geometry where
  path : Path
  tail : Tail
  exclusion : E
  deriving DecidableEq, Repr

def geometry (pattern : Pattern) : Geometry :=
  ⟨pattern.path, pattern.tail, pattern.exclusion⟩

def geometryPoint (shape : Geometry) (location : Path) : Prop :=
  ∃ suffix, shape.path ++ suffix = location ∧ allows shape.tail shape.exclusion suffix

def point (pattern : Pattern) (location : Path) : Prop := geometryPoint (geometry pattern) location

def represents (pattern : Pattern) (base mark : Nat) (location : Path) : Prop :=
  base = pattern.base ∧ slotAdmits pattern.slot mark ∧ point pattern location

def validActual (forward : Bool) (raw : Pattern) : Prop :=
  (raw.tail = .may → raw.exclusion = []) ∧ (raw.tail = .must → forward = true)

def normalizeSelector (selector : Pattern) : Pattern :=
  match selector.slot, selector.tail with
  | .flow _, .star => {selector with exclusion := []}
  | _, _ => selector

theorem selector_base_path_slot_tail_unchanged (selector : Pattern) :
    (normalizeSelector selector).base = selector.base ∧
    (normalizeSelector selector).path = selector.path ∧
    (normalizeSelector selector).slot = selector.slot ∧
    (normalizeSelector selector).tail = selector.tail := by
  cases selector with
  | mk base path tail slot excluded => cases slot <;> cases tail <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem concrete_selector_E_unchanged (base : Nat) (path : Path) (tail : Tail)
    (mark : Nat) (excluded : E) :
    normalizeSelector ⟨base,path,tail,.full mark,excluded⟩ =
      ⟨base,path,tail,.full mark,excluded⟩ := by cases tail <;> rfl

theorem FLOW_STAR_selector_E_only_is_cleared (base : Nat) (path : Path)
    (mx : List Nat) (excluded : E) :
    normalizeSelector ⟨base,path,.star,.flow mx,excluded⟩ =
      ⟨base,path,.star,.flow mx,[]⟩ := rfl

theorem selector_normalization_keeps_requested_points (selector : Pattern) (location : Path)
    (old : point selector location) : point (normalizeSelector selector) location := by
  cases selector with
  | mk base path tail slot excluded =>
    cases slot <;> cases tail
    all_goals first
      | exact old
      | obtain ⟨suffix,same,_⟩ := old
        exact ⟨suffix,same,admits_empty suffix⟩

theorem selector_normalization_keeps_requested_membership (selector : Pattern)
    (base mark : Nat) (location : Path) (old : represents selector base mark location) :
    represents (normalizeSelector selector) base mark location := by
  have headers := selector_base_path_slot_tail_unchanged selector
  exact ⟨old.1.trans headers.1.symm, by simpa only [headers.2.2.1] using old.2.1,
    selector_normalization_keeps_requested_points selector location old.2.2⟩

def sameHead (raw selector : Pattern) : Geometry :=
  match raw.tail, selector.tail with
  | .may, .exact => ⟨raw.path,.exact,[]⟩
  | .must, .exact => ⟨raw.path,.exact,
      match raw.slot with | .flow _ => raw.exclusion | .full _ => []⟩
  | .must, .star => ⟨raw.path,.must,raw.exclusion ++ selector.exclusion⟩
  | _, _ => geometry raw

def rebase (raw selector : Pattern) : Geometry :=
  if selector.tail = .exact then ⟨selector.path,.exact,[]⟩
  else ⟨selector.path,raw.tail,
    if raw.tail = .must ∧ selector.tail = .star then selector.exclusion else []⟩

def selectGeometry (raw selector : Pattern) : Option Geometry :=
  if raw.path = selector.path then some (sameHead raw selector)
  else if selector.path.IsPrefix raw.path then
    if allows selector.tail selector.exclusion (raw.path.drop selector.path.length)
      then some (geometry raw) else none
  else if raw.path.IsPrefix selector.path then
    if raw.tail = .exact then none
    else if admits raw.exclusion (selector.path.drop raw.path.length) then
      if raw.tail = .star then some (geometry raw) else some (rebase raw selector)
    else none
  else none

def install (raw : Fact) (selected : Geometry) : Fact :=
  {raw with path := selected.path, tail := selected.tail, exclusion := selected.exclusion}

def meetExit (forward : Bool) (raw : Fact) (selector : Pattern) : Option Fact :=
  if selector.tail = .must ∨ (raw.tail = .must ∧ forward = false) then none
  else if selector.base ≠ raw.base ∨ slotsMeet selector.slot raw.slot = false then none
  else (selectGeometry raw.toPattern (normalizeSelector selector)).map (install raw)

theorem installed_metadata (raw : Fact) (selected : Geometry) :
    (install raw selected).base = raw.base ∧
    (install raw selected).slot = raw.slot ∧
    (install raw selected).layer = raw.layer ∧ (install raw selected).h = raw.h := ⟨rfl,rfl,rfl,rfl⟩

theorem meet_preserves_layer_slot_H (forward : Bool) (raw kept : Fact) (selector : Pattern)
    (accepted : meetExit forward raw selector = some kept) :
    kept.base = raw.base ∧ kept.slot = raw.slot ∧ kept.layer = raw.layer ∧ kept.h = raw.h := by
  unfold meetExit at accepted
  split at accepted
  next => cases accepted
  next =>
    split at accepted
    next => cases accepted
    next =>
      cases selected : selectGeometry raw.toPattern (normalizeSelector selector) with
      | none => simp only [selected,Option.map_none] at accepted; cases accepted
      | some value =>
        simp only [selected,Option.map_some,Option.some.injEq] at accepted
        cases accepted
        exact installed_metadata raw value

theorem meet_never_creates_a_full_mark (forward : Bool) (raw kept : Fact) (selector : Pattern)
    (accepted : meetExit forward raw selector = some kept) (mark : Nat)
    (present : slotAdmits kept.slot mark) : slotAdmits raw.slot mark := by
  simpa only [(meet_preserves_layer_slot_H forward raw kept selector accepted).2.1] using present

theorem backwards_MUST_is_rejected (raw : Fact) (selector : Pattern) (uniform : raw.tail = .must) :
    meetExit false raw selector = none := by simp [meetExit,uniform]

theorem selector_MUST_is_rejected (forward : Bool) (raw : Fact) (selector : Pattern)
    (uniform : selector.tail = .must) : meetExit forward raw selector = none := by
  simp [meetExit,uniform]

theorem MAY_same_head_EXACT (base : Nat) (path : Path) (slot : Slot) :
    sameHead ⟨base,path,.may,slot,[]⟩ ⟨base,path,.exact,slot,[]⟩ =
      ⟨path,.exact,[]⟩ := rfl

theorem FLOW_MUST_same_head_EXACT_keeps_E (base : Nat) (path : Path)
    (mx : List Nat) (excluded : E) :
    sameHead ⟨base,path,.must,.flow mx,excluded⟩ ⟨base,path,.exact,.flow mx,[]⟩ =
      ⟨path,.exact,excluded⟩ := rfl

theorem full_MUST_same_head_EXACT_clears_E (base : Nat) (path : Path)
    (mark : Nat) (excluded : E) :
    sameHead ⟨base,path,.must,.full mark,excluded⟩ ⟨base,path,.exact,.full mark,[]⟩ =
      ⟨path,.exact,[]⟩ := rfl

theorem MUST_same_head_STAR_unions_E (base : Nat) (path : Path)
    (slot : Slot) (left right : E) :
    sameHead ⟨base,path,.must,slot,left⟩ ⟨base,path,.star,slot,right⟩ =
      ⟨path,.must,left ++ right⟩ := rfl

theorem EXACT_and_STAR_stay_whole (raw selector : Pattern)
    (precise : raw.tail = .exact ∨ raw.tail = .star) : sameHead raw selector = geometry raw := by
  rcases precise with h | h <;> simp [sameHead,h]

theorem same_head_keeps_every_requested_point (raw selector : Pattern) (location : Path)
    (same : raw.path = selector.path) (fromRaw : point raw location)
    (requested : point selector location) : geometryPoint (sameHead raw selector) location := by
  obtain ⟨suffix,rawAt,rawAllows⟩ := fromRaw
  obtain ⟨other,selectorAt,selectorAllows⟩ := requested
  change raw.path ++ suffix = location at rawAt
  change allows raw.tail raw.exclusion suffix at rawAllows
  change selector.path ++ other = location at selectorAt
  change allows selector.tail selector.exclusion other at selectorAllows
  have sameOther : raw.path ++ other = location := by rw [same]; exact selectorAt
  have equalSuffix : suffix = other := List.append_cancel_left (rawAt.trans sameOther.symm)
  subst other
  have rawPoint : geometryPoint (geometry raw) location := ⟨suffix,rawAt,rawAllows⟩
  cases tailRaw : raw.tail with
  | exact => simpa only [sameHead,tailRaw] using rawPoint
  | star => simpa only [sameHead,tailRaw] using rawPoint
  | may =>
    cases tailSelector : selector.tail with
    | exact =>
      simp only [sameHead,tailRaw,tailSelector]
      exact ⟨suffix,rawAt,by simpa only [allows,tailSelector] using selectorAllows⟩
    | star => simpa only [sameHead,tailRaw,tailSelector] using rawPoint
    | may => simpa only [sameHead,tailRaw,tailSelector] using rawPoint
    | must => simpa only [sameHead,tailRaw,tailSelector] using rawPoint
  | must =>
    cases tailSelector : selector.tail with
    | exact =>
      simp only [sameHead,tailRaw,tailSelector]
      exact ⟨suffix,rawAt,by simpa only [allows,tailSelector] using selectorAllows⟩
    | star =>
      simp only [sameHead,tailRaw,tailSelector]
      refine ⟨suffix,rawAt,?_⟩
      change admits (raw.exclusion ++ selector.exclusion) suffix
      exact (admits_union _ _ _).mpr ⟨by simpa [allows,tailRaw] using rawAllows,
        by simpa [allows,tailSelector] using selectorAllows⟩
    | may => simpa only [sameHead,tailRaw,tailSelector] using rawPoint
    | must => simpa only [sameHead,tailRaw,tailSelector] using rawPoint

theorem rebase_keeps_selector_points (raw selector : Pattern) (location : Path)
    (uncorrelated : raw.tail = .may ∨ raw.tail = .must) (requested : point selector location) :
    geometryPoint (rebase raw selector) location := by
  obtain ⟨suffix,atPath,allowed⟩ := requested
  have original : point selector location := ⟨suffix,atPath,allowed⟩
  rcases uncorrelated with rawTail | rawTail
  all_goals
    cases selectorTail : selector.tail
    all_goals first
      | simpa [rebase,rawTail,selectorTail,point,geometry,geometryPoint,allows] using original
      | simpa [rebase,rawTail,selectorTail,geometryPoint,allows,admits_empty] using
          (show ∃ s, selector.path ++ s = location from ⟨suffix,atPath⟩)

theorem point_head_is_prefix (pattern : Pattern) (location : Path) (atPoint : point pattern location) :
    pattern.path.IsPrefix location := by
  obtain ⟨suffix,same,_⟩ := atPoint
  exact ⟨suffix,same⟩

theorem comparable_prefixes (left right leftSuffix rightSuffix : Path)
    (same : left ++ leftSuffix = right ++ rightSuffix) :
    left.IsPrefix right ∨ right.IsPrefix left := by
  induction left generalizing right with
  | nil => exact Or.inl ⟨right,rfl⟩
  | cons first rest ih =>
    cases right with
    | nil => exact Or.inr ⟨first :: rest,rfl⟩
    | cons other later =>
      have heads : first = other := (List.cons.inj same).1
      subst other
      have tails : rest ++ leftSuffix = later ++ rightSuffix := (List.cons.inj same).2
      rcases ih later tails with ⟨suffix,witness⟩ | ⟨suffix,witness⟩
      · exact Or.inl ⟨suffix,by simpa only [List.cons_append] using congrArg (List.cons first) witness⟩
      · exact Or.inr ⟨suffix,by simpa only [List.cons_append] using congrArg (List.cons first) witness⟩

theorem prefix_append_drop (left right : Path) (isPref : left.IsPrefix right) :
    left ++ right.drop left.length = right := by
  obtain ⟨suffix,same⟩ := isPref
  rw [← same,List.drop_append_length]

theorem selector_allows_candidate_head (raw selector : Pattern) (location : Path)
    (isPref : selector.path.IsPrefix raw.path) (fromRaw : point raw location)
    (requested : point selector location) :
    allows selector.tail selector.exclusion (raw.path.drop selector.path.length) := by
  obtain ⟨suffix,rawAt,_⟩ := fromRaw
  obtain ⟨other,selectorAt,allowed⟩ := requested
  change raw.path ++ suffix = location at rawAt
  change selector.path ++ other = location at selectorAt
  change allows selector.tail selector.exclusion other at allowed
  have head := prefix_append_drop selector.path raw.path isPref
  have path : selector.path ++ (raw.path.drop selector.path.length ++ suffix) = location := by
    rw [← List.append_assoc,head,rawAt]
  have tailEq : raw.path.drop selector.path.length ++ suffix = other :=
    List.append_cancel_left (path.trans selectorAt.symm)
  rw [← tailEq] at allowed
  exact allows_prefix _ _ _ _ allowed

theorem actual_allows_selector_head (raw selector : Pattern) (location : Path)
    (isPref : raw.path.IsPrefix selector.path) (fromRaw : point raw location)
    (requested : point selector location) :
    allows raw.tail raw.exclusion (selector.path.drop raw.path.length) :=
  selector_allows_candidate_head selector raw location isPref requested fromRaw

theorem selection_keeps_every_requested_point (raw selector : Pattern) (location : Path)
    (mayEmpty : raw.tail = .may → raw.exclusion = [])
    (fromRaw : point raw location) (requested : point selector location) :
    ∃ selected, selectGeometry raw selector = some selected ∧ geometryPoint selected location := by
  by_cases same : raw.path = selector.path
  · exact ⟨sameHead raw selector,by simp [selectGeometry,same],
      same_head_keeps_every_requested_point raw selector location same fromRaw requested⟩
  · by_cases below : selector.path.IsPrefix raw.path
    · have allowed := selector_allows_candidate_head raw selector location below fromRaw requested
      exact ⟨geometry raw,by simp [selectGeometry,same,below,allowed],fromRaw⟩
    · by_cases above : raw.path.IsPrefix selector.path
      · have allowed := actual_allows_selector_head raw selector location above fromRaw requested
        cases rawTail : raw.tail with
        | exact =>
          obtain ⟨suffix,atRaw,empty⟩ := fromRaw
          have noSuffix : suffix = [] := by simpa [geometry,allows,rawTail] using empty
          have locationEq : location = raw.path := by simpa [geometry,noSuffix] using atRaw.symm
          have impossible := point_head_is_prefix selector location requested
          rw [locationEq] at impossible
          exact False.elim (below impossible)
        | star =>
          have admitted : admits raw.exclusion (selector.path.drop raw.path.length) := by
            simpa [allows,rawTail] using allowed
          exact ⟨geometry raw,by simp [selectGeometry,same,below,above,rawTail,admitted],fromRaw⟩
        | may =>
          have admitted : admits raw.exclusion (selector.path.drop raw.path.length) := by
            rw [mayEmpty rawTail]; exact admits_empty _
          exact ⟨rebase raw selector,by simp [selectGeometry,same,below,above,rawTail,admitted],
            rebase_keeps_selector_points raw selector location (Or.inl rawTail) requested⟩
        | must =>
          have admitted : admits raw.exclusion (selector.path.drop raw.path.length) := by
            simpa [allows,rawTail] using allowed
          exact ⟨rebase raw selector,by simp [selectGeometry,same,below,above,rawTail,admitted],
            rebase_keeps_selector_points raw selector location (Or.inr rawTail) requested⟩
      · obtain ⟨left,hl,_⟩ := fromRaw
        obtain ⟨right,hr,_⟩ := requested
        rcases comparable_prefixes raw.path selector.path left right (hl.trans hr.symm) with h | h
        · exact False.elim (above h)
        · exact False.elim (below h)

theorem meet_retains_requested_membership (forward : Bool) (raw : Fact) (selector : Pattern)
    (base mark : Nat) (location : Path) (legal : validActual forward raw.toPattern)
    (notMustSelector : selector.tail ≠ .must)
    (fromRaw : represents raw.toPattern base mark location)
    (requested : represents selector base mark location) :
    ∃ kept, meetExit forward raw selector = some kept ∧
      represents kept.toPattern base mark location ∧ kept.layer = raw.layer ∧ kept.h = raw.h := by
  have normalized := selector_normalization_keeps_requested_membership selector base mark location requested
  have baseEq : selector.base = raw.base := requested.1.symm.trans fromRaw.1
  have markGate : slotsMeet selector.slot raw.slot = true :=
    common_full_mark_passes selector.slot raw.slot mark requested.2.1 fromRaw.2.1
  have validDirection : ¬ (raw.tail = .must ∧ forward = false) := by
    intro bad
    have yes := legal.2 bad.1
    rw [yes] at bad
    cases bad.2
  obtain ⟨selected,chosen,atPoint⟩ := selection_keeps_every_requested_point raw.toPattern
    (normalizeSelector selector) location legal.1 fromRaw.2.2 normalized.2.2
  refine ⟨install raw selected,?_,?_,rfl,rfl⟩
  · simp [meetExit,notMustSelector,validDirection,baseEq,markGate,chosen]
  · exact ⟨fromRaw.1,fromRaw.2.1,atPoint⟩

/-! The counted cut is exactly the pinned Geometry.limit on the scalar shape. -/
def scalarShape (raw : Fact) : RelativeRestriction.Scalar :=
  ⟨⟨raw.base,raw.path,raw.tail,0⟩,raw.layer,raw.h⟩

def cut (budget : Nat) (raw : Fact) : Fact :=
  if RelativeRestriction.depth raw.path ≤ budget then raw
  else ⟨⟨raw.base,RelativeRestriction.clip budget raw.path,.may,raw.slot,[]⟩,
    .demand,raw.h⟩

theorem cut_is_pinned_scalar_limit (budget : Nat) (raw : Fact) :
    scalarShape (cut budget raw) = RelativeRestriction.limit budget (scalarShape raw) := by
  by_cases within : RelativeRestriction.depth raw.path ≤ budget
  · simp [cut,RelativeRestriction.limit,scalarShape,within]
  · simp [cut,RelativeRestriction.limit,scalarShape,within]

theorem cut_preserves_base_slot_H (budget : Nat) (raw : Fact) :
    (cut budget raw).base = raw.base ∧ (cut budget raw).slot = raw.slot ∧
    (cut budget raw).h = raw.h := by unfold cut; split <;> exact ⟨rfl,rfl,rfl⟩

theorem cut_depth_bound (budget : Nat) (raw : Fact) :
    RelativeRestriction.depth (cut budget raw).path ≤ budget := by
  have bound := RelativeRestriction.limit_depth_bound budget (scalarShape raw)
  rw [← cut_is_pinned_scalar_limit] at bound
  exact bound

theorem within_cut_is_identity (budget : Nat) (raw : Fact)
    (within : RelativeRestriction.depth raw.path ≤ budget) : cut budget raw = raw := by
  simp [cut,within]

theorem real_cut_is_MAY_DEMAND_EmptyE (budget : Nat) (raw : Fact)
    (overflow : ¬ RelativeRestriction.depth raw.path ≤ budget) :
    (cut budget raw).tail = .may ∧ (cut budget raw).layer = .demand ∧
    (cut budget raw).exclusion = [] := by simp [cut,overflow]

theorem cut_never_promotes_DEMAND (budget : Nat) (raw : Fact) (old : raw.layer = .demand) :
    (cut budget raw).layer = .demand := by unfold cut; split <;> simp_all

theorem NORMAL_cut_was_unchanged (budget : Nat) (raw : Fact)
    (normal : (cut budget raw).layer = .normal) : cut budget raw = raw := by
  by_cases within : RelativeRestriction.depth raw.path ≤ budget
  · exact within_cut_is_identity budget raw within
  · simp [cut, within] at normal

theorem cut_retains_possible_membership (budget : Nat) (raw : Fact)
    (base mark : Nat) (location : Path) (present : represents raw.toPattern base mark location) :
    represents (cut budget raw).toPattern base mark location := by
  unfold cut
  split
  · exact present
  · obtain ⟨suffix,atPath,_⟩ := present.2.2
    change raw.path ++ suffix = location at atPath
    obtain ⟨lost,clipEq⟩ := RelativeRestriction.clip_is_prefix budget raw.path
    refine ⟨present.1,present.2.1,lost ++ suffix,?_,?_⟩
    · change RelativeRestriction.clip budget raw.path ++ (lost ++ suffix) = location
      rw [← List.append_assoc,clipEq,atPath]
    · change allows .may [] (lost ++ suffix)
      trivial

def pairBudget (global : Nat) (selector : Pattern) : Nat :=
  min global (RelativeRestriction.depth selector.path + 1)

theorem positive_pair_budget (global : Nat) (selector : Pattern) (positive : 0 < global) :
    0 < pairBudget global selector :=
  Nat.le_min.mpr ⟨positive,Nat.succ_le_succ (Nat.zero_le _)⟩

theorem pair_budget_limits (global : Nat) (selector : Pattern) :
    pairBudget global selector ≤ global ∧
    pairBudget global selector ≤ RelativeRestriction.depth selector.path + 1 :=
  ⟨Nat.min_le_left _ _,Nat.min_le_right _ _⟩

def restrictData (forward : Bool) (global : Nat) (raw : Fact) (selector : Pattern) : Option Fact :=
  (meetExit forward raw selector).map (cut (pairBudget global selector))

theorem restricted_has_one_computed_meet (forward : Bool) (global : Nat)
    (raw kept : Fact) (selector : Pattern)
    (accepted : restrictData forward global raw selector = some kept) :
    ∃ selected, meetExit forward raw selector = some selected ∧
      kept = cut (pairBudget global selector) selected := by
  unfold restrictData at accepted
  cases selected : meetExit forward raw selector with
  | none => simp only [selected,Option.map_none] at accepted; cases accepted
  | some value =>
    simp only [selected,Option.map_some,Option.some.injEq] at accepted
    exact ⟨value,rfl,accepted.symm⟩

theorem restricted_depth_uses_its_own_exit (forward : Bool) (global : Nat)
    (raw kept : Fact) (selector : Pattern)
    (accepted : restrictData forward global raw selector = some kept) :
    RelativeRestriction.depth kept.path ≤ global ∧
    RelativeRestriction.depth kept.path ≤ RelativeRestriction.depth selector.path + 1 := by
  obtain ⟨selected,_,same⟩ := restricted_has_one_computed_meet forward global raw kept selector accepted
  rw [same]
  have bounded := cut_depth_bound (pairBudget global selector) selected
  exact ⟨Nat.le_trans bounded (pair_budget_limits global selector).1,
    Nat.le_trans bounded (pair_budget_limits global selector).2⟩

theorem restricted_retains_requested_membership (forward : Bool) (global : Nat)
    (raw : Fact) (selector : Pattern) (base mark : Nat) (location : Path)
    (legal : validActual forward raw.toPattern) (notMustSelector : selector.tail ≠ .must)
    (fromRaw : represents raw.toPattern base mark location)
    (requested : represents selector base mark location) :
    ∃ kept, restrictData forward global raw selector = some kept ∧
      represents kept.toPattern base mark location := by
  obtain ⟨selected,found,present,_,_⟩ := meet_retains_requested_membership forward raw selector
    base mark location legal notMustSelector fromRaw requested
  exact ⟨cut (pairBudget global selector) selected,by simp [restrictData,found],
    cut_retains_possible_membership _ selected base mark location present⟩

/-! Typed controls and exhaustive row union. Keys/owner encode the complete interface. -/
inductive Original where
  | zero
  | single (member : Nat)
  | nd (members : List Nat)
  deriving DecidableEq, Repr
inductive Entry where
  | zero | target | data (selector : Pattern)
  deriving DecidableEq, Repr
inductive Exit where
  | zero | data (selector : Pattern)
  deriving DecidableEq, Repr
inductive Candidate where
  | data (value : Fact)
  | reach (layer : Layer)
  | demandTarget
  deriving DecidableEq, Repr
structure Row where
  owner : Nat
  entry : Entry
  exit : Exit
  deriving DecidableEq, Repr
structure Publication where
  owner : Nat
  original : Original
  result : Candidate
  deriving DecidableEq, Repr

def entryOK (image : Pattern → Nat → Bool) : Entry → Original → Bool
  | .zero, .zero | .target, .zero => true
  | .data selector, .single member => image selector member
  | .data selector, .nd members => members.any (image selector)
  | _, _ => false

theorem DATA_ND_ticket_is_one_member (image : Pattern → Nat → Bool)
    (selector : Pattern) (members : List Nat) :
    entryOK image (.data selector) (.nd members) = true ↔
      ∃ member, member ∈ members ∧ image selector member = true := by
  simp [entryOK,List.any_eq_true]

theorem control_entry_cannot_admit_DATA_original (image : Pattern → Nat → Bool)
    (member : Nat) : entryOK image .zero (.single member) = false ∧
      entryOK image .target (.single member) = false := ⟨rfl,rfl⟩

def exitResult (forward : Bool) (global : Nat) (raw : Candidate) : Exit → Option Candidate
  | .zero => match raw with
    | .reach layer => some (.reach layer)
    | .demandTarget => some .demandTarget
    | .data _ => none
  | .data selector => match raw with
    | .data value => (restrictData forward global value selector).map Candidate.data
    | _ => none

def rowResult (image : Pattern → Nat → Bool) (forward : Bool) (global owner : Nat)
    (original : Original) (raw : Candidate) (row : Row) : Option Publication :=
  if row.owner = owner ∧ entryOK image row.entry original = true then
    (exitResult forward global raw row.exit).map fun kept => ⟨owner,original,kept⟩
  else none

def rowUnion (image : Pattern → Nat → Bool) (forward : Bool) (global owner : Nat)
    (original : Original) (raw : Candidate) (rows : List Row) : List Publication :=
  rows.filterMap (rowResult image forward global owner original raw)

theorem whole_original_and_owner_kept (image : Pattern → Nat → Bool) (forward : Bool)
    (global owner : Nat) (original : Original) (raw : Candidate) (row : Row)
    (kept : Publication) (accepted : rowResult image forward global owner original raw row = some kept) :
    kept.original = original ∧ kept.owner = owner := by
  unfold rowResult at accepted
  split at accepted
  next =>
    cases result : exitResult forward global raw row.exit with
    | none => simp only [result,Option.map_none] at accepted; cases accepted
    | some value =>
      simp only [result,Option.map_some,Option.some.injEq] at accepted
      cases accepted; exact ⟨rfl,rfl⟩
  next => cases accepted

theorem every_union_result_has_one_complete_row (image : Pattern → Nat → Bool) (forward : Bool)
    (global owner : Nat) (original : Original) (raw : Candidate) (rows : List Row)
    (kept : Publication) (present : kept ∈ rowUnion image forward global owner original raw rows) :
    ∃ row, row ∈ rows ∧ rowResult image forward global owner original raw row = some kept :=
  List.mem_filterMap.mp present

theorem each_complete_row_result_is_in_union (image : Pattern → Nat → Bool) (forward : Bool)
    (global owner : Nat) (original : Original) (raw : Candidate) (rows : List Row)
    (row : Row) (kept : Publication) (member : row ∈ rows)
    (accepted : rowResult image forward global owner original raw row = some kept) :
    kept ∈ rowUnion image forward global owner original raw rows :=
  List.mem_filterMap.mpr ⟨row,member,accepted⟩

theorem row_union_is_append_not_cross_product (image : Pattern → Nat → Bool) (forward : Bool)
    (global owner : Nat) (original : Original) (raw : Candidate) (left right : List Row) :
    rowUnion image forward global owner original raw (left ++ right) =
      rowUnion image forward global owner original raw left ++
      rowUnion image forward global owner original raw right := by
  simp [rowUnion,List.filterMap_append]

theorem ZERO_exit_rejects_DATA (forward : Bool) (global : Nat) (raw : Fact) :
    exitResult forward global (.data raw) .zero = none := rfl

theorem DATA_exit_rejects_control (forward : Bool) (global : Nat) (layer : Layer) (selector : Pattern) :
    exitResult forward global (.reach layer) (.data selector) = none ∧
      exitResult forward global .demandTarget (.data selector) = none := ⟨rfl,rfl⟩

theorem ZERO_exit_keeps_typed_controls (forward : Bool) (global : Nat) (layer : Layer) :
    exitResult forward global (.reach layer) .zero = some (.reach layer) ∧
      exitResult forward global .demandTarget .zero = some .demandTarget := ⟨rfl,rfl⟩

theorem ZERO_original_DATA_is_still_intersected_and_capped
    (image : Pattern → Nat → Bool) (forward : Bool) (global owner : Nat)
    (raw : Fact) (selector : Pattern) :
    rowResult image forward global owner .zero (.data raw) ⟨owner,.target,.data selector⟩ =
      (restrictData forward global raw selector).map
        (fun kept => ⟨owner,.zero,Candidate.data kept⟩) := by
  simp [rowResult,entryOK,exitResult,Option.map_map,Function.comp_def]

/-! Executable witnesses cover differing budgets and the selected E/slot cells. -/
def source3 : Fact := ⟨⟨7,[.field 1,.field 2,.field 3],.exact,.full 11,[]⟩,.normal,false⟩
def precise : Pattern := ⟨7,[.field 1,.field 2,.field 3],.exact,.full 11,[]⟩
def shallow : Pattern := ⟨7,[.field 1],.may,.full 11,[]⟩
def witnessEntry : Entry := .data ⟨8,[],.may,.full 11,[]⟩
def twoRows : List Row := [⟨4,witnessEntry,.data precise⟩,⟨4,witnessEntry,.data shallow⟩]

theorem both_budgets_keep_distinct_final_results :
    rowUnion (fun _ _ => true) true 3 4 (.single 5) (.data source3) twoRows =
      [⟨4,.single 5,.data source3⟩,
       ⟨4,.single 5,.data ⟨⟨7,[.field 1,.field 2],.may,.full 11,[]⟩,.demand,false⟩⟩] := by decide

theorem first_DATA_result_does_not_saturate :
    rowUnion (fun _ _ => true) true 3 4 (.single 5) (.data source3) twoRows ≠
      rowUnion (fun _ _ => true) true 3 4 (.single 5) (.data source3) (twoRows.take 1) := by decide

theorem selector_FLOW_STAR_E_is_ignored_but_concrete_STAR_E_is_not :
    meetExit true ⟨⟨1,[.field 6],.exact,.full 9,[]⟩,.normal,false⟩
      ⟨1,[],.star,.flow [],[.field 6]⟩ =
        some ⟨⟨1,[.field 6],.exact,.full 9,[]⟩,.normal,false⟩ ∧
    meetExit true ⟨⟨1,[.field 6],.exact,.full 9,[]⟩,.normal,false⟩
      ⟨1,[],.star,.full 9,[.field 6]⟩ = none := by decide

theorem wrong_FULL_mark_is_not_created :
    meetExit true ⟨⟨1,[],.star,.full 9,[]⟩,.demand,false⟩
      ⟨1,[],.may,.full 10,[]⟩ = none := by decide

theorem correlated_STAR_is_not_exact_set_intersection :
    meetExit true ⟨⟨1,[],.star,.full 9,[]⟩,.demand,false⟩
      ⟨1,[],.exact,.full 9,[]⟩ = some ⟨⟨1,[],.star,.full 9,[]⟩,.demand,false⟩ ∧
    point ⟨1,[],.star,.full 9,[]⟩ [.field 6] ∧
      ¬ point ⟨1,[],.exact,.full 9,[]⟩ [.field 6] := by
  refine ⟨by decide,?_,?_⟩
  · refine ⟨[.field 6],rfl,?_⟩
    change admits [] [.field 6]
    exact admits_empty _
  · rintro ⟨suffix,same,empty⟩
    have noSuffix : suffix = [] := empty
    subst suffix
    cases same

theorem concrete_selector_does_not_narrow_FLOW_slot :
    meetExit true ⟨⟨1,[],.star,.flow [],[]⟩,.normal,false⟩
      ⟨1,[],.may,.full 10,[]⟩ = some ⟨⟨1,[],.star,.flow [],[]⟩,.normal,false⟩ := by decide

end AnnotatedC5Exit
