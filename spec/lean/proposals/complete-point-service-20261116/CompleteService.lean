import CompletePoint
import CompleteClosure
namespace CompleteService
open CompletePoint NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

inductive Node where
  | entry (q : Seed)
  | result (c : Value)
  deriving DecidableEq

def next : Node → List Node
  | .entry q => (colors.flatMap fun m => gen m q).map Node.result
  | .result _ => []
def owned (q : Seed) : List Node := .entry q :: next (.entry q)
def returned : Node → Bool | .entry _ => false | .result _ => true

def service (current : List CompletePoint.Edge) (q : Seed) : Node → Bool
  | .entry _ => true
  | .result c => !c.demand && !c.h && current.any (fun e => decide (e.1=q.ap ∧ e.2=c))

theorem leaf_closure_certificate (current : List CompletePoint.Edge) (q : Seed)
    (ok : completePoint current q = true) :
    CompleteClosure.check next [.entry q] (owned q) returned (service current q) = true := by
  have allReturns : (colors.flatMap fun m => gen m q).all (fun c =>
      !c.demand && !c.h && current.any (fun e => decide (e.1=q.ap ∧ e.2=c))) = true := by
    have h := ok
    simp only [completePoint,Bool.and_eq_true] at h
    exact h.2
  -- The seed and every one-step return are owned. There are no omitted steps.
  simp only [CompleteClosure.check,Bool.and_eq_true]
  constructor
  · constructor
    · simp [owned]
    · apply List.all_eq_true.mpr
      intro n hn
      simp only [owned,List.mem_cons] at hn
      rcases hn with seed | exit
      · subst n
        apply List.all_eq_true.mpr
        intro t ht
        exact decide_eq_true (List.mem_cons_of_mem _ ht)
      · rcases List.mem_map.mp exit with ⟨c,_,eq⟩
        subst n
        simp [next]
  · apply List.all_eq_true.mpr
    intro n hn
    simp only [owned,List.mem_cons] at hn
    rcases hn with seed | exit
    · subst n; rfl
    · rcases List.mem_map.mp exit with ⟨c,hc,eq⟩
      subst n
      exact List.all_eq_true.mp allReturns c hc

theorem any_strong_return_has_an_admitted_NORMAL_row (current : List CompletePoint.Edge) (q : Seed)
    (ok : completePoint current q = true) (c : Value)
    (reached : CompleteClosure.Reach next [.entry q] (.result c)) :
    c.demand = false ∧ c.h = false ∧ ∃ e ∈ current, e.1=q.ap ∧ e.2=c := by
  have all := CompleteClosure.every_reachable_return_is_covered next [.entry q] (owned q)
    returned (service current q) (leaf_closure_certificate current q ok) (.result c) reached rfl
  simp only [service,Bool.and_eq_true,Bool.not_eq_true',List.any_eq_true,decide_eq_true_eq] at all
  exact ⟨all.1.1,all.1.2,all.2⟩

-- The checker rejects incomplete services; it does not guess from a positive child.
def point (m : Color) : Seed := ⟨fact p [f,g] .exact m,false⟩
def answer (m : Color) : CompletePoint.Edge := ((point m).ap,value ret [h] .must m.flip false)

theorem checked_complete_point (m : Color) : completePoint [answer m] (point m)=true := by
  cases m <;> decide +kernel

theorem missing_admitted_return_is_not_complete (m : Color) : completePoint [] (point m)=false := by
  cases m <;> decide +kernel

theorem demanded_answer_is_not_a_NORMAL_service (m : Color) :
    completePoint [((point m).ap,value ret [h] .must m.flip)] (point m)=false := by
  cases m <;> decide +kernel

theorem wrong_point_is_not_a_complete_service (m : Color) :
    completePoint [(fact p [f] .exact m,(answer m).2)] (point m)=false := by
  cases m <;> decide +kernel

theorem a_shortened_query_cannot_certify_the_exact_input (m : Color) :
    completePoint [answer m] (star p [f] m)=false := by cases m <;> decide +kernel

theorem the_fine_query_is_already_in_C2 (m : Color) :
    HeadPolicy.emit 3 2 false (fact p [f] .ne m) ⟨(point m).ap,false⟩=[point m] := by
  cases m <;> decide +kernel

theorem no_entry_cap_exception_is_required (m : Color) :
    (point m).ap.path.length≤2 ∧
    (point m).ap.path.length≤(fact p [f] .ne m).path.length+1 := by cases m <;> decide +kernel

theorem all_old_emitters_and_transfers_are_reused (m : Color) (q : Seed) :
    gen m q = ExactGuard.gen m q := rfl

def critical (m : Color) : CompletePoint.Edge := (fact p [f] .star m,value ret [] .may m.flip)
def actual (m : Color) : Offered := ⟨(point m).ap,false⟩

theorem omit_only_the_ready_coarse_return (m : Color) :
    suppress 3 [(point m).ap] (actual m) (critical m)=true := by cases m <;> decide +kernel

theorem no_ready_certificate_means_no_pruning (run : Nat) (a : Offered) (e : CompletePoint.Edge) :
    suppress run [] a e=false := by simp [suppress]

theorem NORMAL_answers_are_never_omitted (run : Nat) (ready : List Ap) (a : Offered) (e : CompletePoint.Edge)
    (normal : e.2.demand=false) : suppress run ready a e=false := by simp [suppress,normal]

theorem protected_answers_are_never_omitted (run : Nat) (ready : List Ap) (a : Offered) (e : CompletePoint.Edge)
    (hFlag : e.2.h=true) : suppress run ready a e=false := by simp [suppress,hFlag]

theorem backward_is_unchanged (run : Nat) (ready : List Ap) (a : Offered) (e : CompletePoint.Edge)
    (back : run % 2=0) : suppress run ready a e=false := by simp [suppress,back]

theorem run1_is_unchanged (ready : List Ap) (a : Offered) (e : CompletePoint.Edge) :
    suppress 1 ready a e=false := by simp [suppress]

theorem abstract_actual_is_unchanged (run : Nat) (ready : List Ap) (a : Offered) (e : CompletePoint.Edge)
    (flow : a.ap.mark=none) : suppress run ready a e=false := by simp [suppress,flow]

theorem provisional_actual_is_unchanged (run : Nat) (ready : List Ap) (a : Offered) (e : CompletePoint.Edge)
    (provisional : a.demand=true) : suppress run ready a e=false := by simp [suppress,provisional]

theorem non_exact_actual_is_unchanged (run : Nat) (ready : List Ap) (a : Offered) (e : CompletePoint.Edge)
    (notExact : a.ap.tail≠.exact) : suppress run ready a e=false := by simp [suppress,notExact]

/-- The optimization only filters existing current rows. No field or key is generated. -/
def keep (run : Nat) (ready : List Ap) (a : Offered) (current : List CompletePoint.Edge) : List CompletePoint.Edge :=
  current.filter (fun e => !suppress run ready a e)

theorem no_extra_row (run : Nat) (ready : List Ap) (a : Offered) (xs : List CompletePoint.Edge) :
    (keep run ready a xs).length≤xs.length := List.length_filter_le _ _

theorem keeps_every_NORMAL (run : Nat) (ready : List Ap) (a : Offered) (xs : List CompletePoint.Edge) (e : CompletePoint.Edge)
    (inside : e ∈ xs) (normal : e.2.demand=false) : e ∈ keep run ready a xs := by
  exact List.mem_filter.mpr ⟨inside,by rw [NORMAL_answers_are_never_omitted _ _ _ _ normal]; rfl⟩

theorem primitive_scope_completeness_is_not_shape_subsumption (m : Color) :
    UniformActual.foldValues false [] [rootMay m.flip,value p [h] .must m.flip false] =
      [rootMay m.flip,value p [h] .must m.flip false] := by cases m <;> decide +kernel

theorem maximal_ready_dominates (run : Nat) (a : Offered) (e : CompletePoint.Edge)
    (ready : List Ap) (no : suppress run [a.ap] a e=false) : suppress run ready a e=false := by
  unfold suppress at *
  simp only [List.any_cons,List.any_nil,decide_true,Bool.or_false] at no
  cases found : ready.any (fun q => decide (q=a.ap))
  · simp [found]
  · simpa only [found] using no

theorem event_subset_is_unchanged (run : Nat) (domains : List Offered) (all : List CompletePoint.Edge)
    (no : domains.all (fun a => all.all (fun e => !suppress run [a.ap] a e))=true)
    (ready : List Ap) (a : Offered) (ha : a ∈ domains) (xs : List CompletePoint.Edge)
    (subset : ∀ e ∈ xs, e ∈ all) : keep run ready a xs=xs := by
  apply List.filter_eq_self.mpr
  intro e he
  have h := List.all_eq_true.mp (List.all_eq_true.mp no a ha) e (subset e he)
  have none : suppress run [a.ap] a e=false := by simpa only [Bool.not_eq_true'] using h
  rw [maximal_ready_dominates run a e ready none]
  rfl

theorem ready_requires_every_NORMAL_service_result_to_be_delivered
    (raw : List Value) (q : Ap) (ok : delivered raw q=true)
    (c : Value) (member : c ∈ colors.flatMap (fun m => gen m ⟨q,false⟩)) :
    c.demand=false ∧ c.h=false ∧
      ∃ n ∈ raw, n={c with ap := {c.ap with base := p}} := by
  have h := List.all_eq_true.mp ok c member
  simp only [Bool.and_eq_true,Bool.not_eq_true',List.any_eq_true,decide_eq_true_eq] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

theorem abstract_owned_query_cannot_certify_a_concrete_service
    (current : List CompletePoint.Edge) (q : Seed) (abstract : q.ap.mark=none) :
    completePoint current q=false := by simp [completePoint,abstract]

end CompleteService
