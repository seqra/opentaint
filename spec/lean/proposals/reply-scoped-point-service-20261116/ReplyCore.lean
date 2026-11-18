import FieldCycle
import CompleteClosure
namespace ReplyCore
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
set_option linter.unusedSimpArgs false

-- Conservative overlap of represented locations. Unknown children with
-- incomparable exclusion sets are never incorrectly declared disjoint.
def geometry : Path → Tail → List Nat → Path → Tail → List Nat → Bool
  | [],ta,ea,[],tb,eb => (admits ta ea [] && admits tb eb []) || (ta != .exact && tb != .exact)
  | [],ta,ea,b::bs,_,_ => admits ta ea (b::bs)
  | a::ps,_,_,[],tb,eb => admits tb eb (a::ps)
  | a::ps,ta,ea,b::bs,tb,eb => a==b && geometry ps ta ea bs tb eb

def overlaps (a b : Ap) : Bool :=
  a.base==b.base && marksMeet a b && geometry a.path a.tail a.e b.path b.tail b.e

theorem geometry_never_misses_a_common_location (pa pb sa sb : Path) (ta tb : Tail)
    (ea eb : List Nat) (same : pa++sa=pb++sb)
    (ha : admits ta ea sa=true) (hb : admits tb eb sb=true) :
    geometry pa ta ea pb tb eb=true := by
  induction pa generalizing pb with
  | nil =>
      cases pb with
      | nil =>
          have eq : sa=sb := same
          subst sb
          cases sa with
          | nil => simp [geometry,ha,hb]
          | cons f rest => cases ta <;> cases tb <;> simp_all [geometry,admits]
      | cons b bs =>
          have eq : sa=b::(bs++sb) := same
          rw [eq] at ha
          simpa only [geometry,admits] using ha
  | cons a ps ih =>
      cases pb with
      | nil =>
          have eq : sb=a::(ps++sa) := same.symm
          rw [eq] at hb
          simpa only [geometry,admits] using hb
      | cons b bs =>
          have eq : a=b ∧ ps++sa=bs++sb := List.cons.inj same
          rcases eq with ⟨eqHead,eqTail⟩
          subst b
          simp only [geometry,beq_self_eq_true,Bool.true_and]
          exact ih bs eqTail

def markPossible (a : Ap) (mark : Nat) : Bool :=
  match a.mark with
  | some t => t==mark
  | none => !a.mx.contains mark

theorem full_mark_meet_is_complete (a b : Ap) (mark : Nat)
    (concrete : b.mark=some mark) (possible : markPossible a mark=true) :
    marksMeet a b=true := by
  cases hm : a.mark <;> simp_all [marksMeet,markPossible]

theorem overlaps_never_misses_a_common_concrete_location (a b : Ap) (mark : Nat)
    (base : a.base=b.base) (concrete : b.mark=some mark)
    (possible : markPossible a mark=true) (location : Path)
    (inA : UniformActual.locationIn a location) (inB : UniformActual.locationIn b location) :
    overlaps a b=true := by
  rcases inA with ⟨sa,ha,aa⟩
  rcases inB with ⟨sb,hb,ab⟩
  have common : a.path++sa=b.path++sb := ha.symm.trans hb
  have geometry := geometry_never_misses_a_common_location a.path b.path sa sb a.tail b.tail a.e b.e common aa ab
  simp only [overlaps,base,beq_self_eq_true,Bool.true_and,
    full_mark_meet_is_complete a b mark concrete possible,geometry]

abbrev Edge := Ap × Value

def focus (raw : List Value) (region : Ap) : List Value :=
  raw.filter (fun c => overlaps c.ap region)

def completeFor (current : List Edge) (q : Seed) (raw : List Value) (region : Ap) : Bool :=
  ScopedCore.eligible q && raw.all ScopedCore.normal &&
    (focus raw region).all (ScopedCore.covered current q)

def received (native : List Value) (raw : List Value) (region : Ap) : Bool :=
  (focus raw region).all fun c => native.any (fun n => decide (n={c with ap := {c.ap with base := AlternatingCondition.p}}))

theorem completion_covers_every_selected_return (current : List Edge) (q : Seed)
    (raw : List Value) (region : Ap) (ok : completeFor current q raw region=true)
    (c : Value) (inside : c∈raw) (selected : overlaps c.ap region=true) :
    ScopedCore.normal c=true ∧ ScopedCore.covered current q c=true := by
  have h := ok
  simp only [completeFor,Bool.and_eq_true] at h
  exact ⟨List.all_eq_true.mp h.1.2 c inside,
    List.all_eq_true.mp h.2 c (List.mem_filter.mpr ⟨inside,selected⟩)⟩

theorem receipt_has_an_actually_applied_NORMAL_image (native raw : List Value)
    (region : Ap) (ok : received native raw region=true)
    (c : Value) (inside : c∈raw) (selected : overlaps c.ap region=true) :
    ∃ n∈native,n={c with ap := {c.ap with base := AlternatingCondition.p}} := by
  rcases List.any_eq_true.mp (List.all_eq_true.mp ok c (List.mem_filter.mpr ⟨inside,selected⟩)) with ⟨n,hn,eq⟩
  exact ⟨n,hn,of_decide_eq_true eq⟩

-- Projection changes only the terminal predicate. Internal closure stays full.
def selected {α : Type} (returned relevant : α → Bool) (s : α) := returned s && relevant s

theorem every_relevant_reachable_return_has_NORMAL_service {α : Type} [DecidableEq α]
    (next : α → List α) (seeds owned service : List α) (returned relevant : α → Bool)
    (covers : α → α → Bool)
    (ok : CompleteClosure.check next seeds owned (selected returned relevant)
      (CompleteClosure.hasWitness service covers)=true)
    (s : α) (reach : CompleteClosure.Reach next seeds s)
    (exit : returned s=true) (needed : relevant s=true) :
    ∃ n∈service,covers n s=true := by
  apply CompleteClosure.a_concrete_normal_service_witness next seeds owned service
    (selected returned relevant) covers ok s reach
  simp [selected,exit,needed]

theorem arbitrary_relevant_continuation_observation_is_preserved {α : Type} [DecidableEq α]
    (next : α → List α) (seeds owned service : List α) (returned relevant : α → Bool)
    (covers : α → α → Bool) (observe : α → Prop)
    (ok : CompleteClosure.check next seeds owned (selected returned relevant)
      (CompleteClosure.hasWitness service covers)=true)
    (native : ∀ n∈service,∀ s,covers n s=true → observe s → observe n)
    (s : α) (reach : CompleteClosure.Reach next seeds s) (exit : returned s=true)
    (needed : relevant s=true) (seen : observe s) : ∃ n∈service,observe n := by
  apply CompleteClosure.caller_observation_is_preserved next seeds owned service
    (selected returned relevant) covers observe ok native s reach _ seen
  simp [selected,exit,needed]

-- No-return-in-this-region is checked on demand, never put in a negative cache.
theorem disjoint_returns_have_no_service_obligation (current : List Edge) (q : Seed)
    (raw : List Value) (region : Ap) (disjoint : ∀ c∈raw,overlaps c.ap region=false) :
    (focus raw region).all (ScopedCore.covered current q)=true := by
  apply List.all_eq_true.mpr
  intro c hc
  have mem := List.mem_filter.mp hc
  rw [disjoint c mem.1] at mem
  cases mem.2

end ReplyCore
