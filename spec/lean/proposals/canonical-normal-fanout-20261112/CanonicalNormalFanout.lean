import Std

namespace CanonicalNormalFanout

-- Pointwise finite-state model of registered targets, admitted initials and
-- start pairs already queued or executed. It does not model AP transfer,
-- liveness extraction, aliases, source rules or native layout construction.
structure State (I T : Type) where
  initials : I → Bool
  targets : T → Bool
  ready : I → T → Bool

def Exact (s : State I T) : Prop :=
  ∀ i t, s.ready i t = (s.initials i && s.targets t)

-- Old initials go to new targets. New initials go to every current target.
-- An already queued/executed pair is retained in this monotone history view.
def offer (s : State I T) (a : I → Bool) (b : T → Bool) : State I T where
  initials i := s.initials i || a i
  targets t := s.targets t || b t
  ready i t := s.ready i t ||
    (s.initials i && !s.targets t && b t) ||
    (!s.initials i && a i && (s.targets t || b t))

private theorem boolean_product : ∀ a b x y r : Bool,
    r = (a && b) →
    (r || (a && !b && y) || (!a && x && (b || y))) =
      ((a || x) && (b || y)) := by decide

theorem offer_exact (s : State I T) (a : I → Bool) (b : T → Bool)
    (h : Exact s) : Exact (offer s a b) := by
  intro i t
  exact boolean_product _ _ _ _ _ (h i t)

def emptyState : State I T where
  initials _ := false
  targets _ := false
  ready _ _ := false

theorem empty_exact : Exact (emptyState : State I T) := by
  intro i t
  rfl

def processOffers (s : State I T) : List ((I → Bool) × (T → Bool)) → State I T
  | [] => s
  | step :: rest => processOffers (offer s step.1 step.2) rest

theorem finite_offer_history_exact (s : State I T) (h : Exact s)
    (history : List ((I → Bool) × (T → Bool))) : Exact (processOffers s history) := by
  induction history generalizing s with
  | nil => exact h
  | cons step rest ih => exact ih (offer s step.1 step.2) (offer_exact s step.1 step.2 h)

theorem registered_initial_is_ready (s : State I T) (h : Exact s)
    (i : I) (t : T) (hi : s.initials i = true) (ht : s.targets t = true) :
    s.ready i t = true := by
  rw [h i t, hi, ht]
  rfl

-- A completed all-route offer starts each admitted initial at each certified
-- target. There is no assumption on its old/new arrival order.
theorem complete_fanout (s : State I T) (a : I → Bool) (b : T → Bool)
    (h : Exact s) (i : I) (t : T) (hi : a i = true) (ht : b t = true) :
    (offer s a b).ready i t = true := by
  rw [offer_exact s a b h i t]
  change ((s.initials i || a i) && (s.targets t || b t)) = true
  rw [hi, ht]
  cases s.initials i <;> cases s.targets t <;> rfl

-- If an old initial independently covered all targets, another arrival cannot
-- be the first start witness for it at one of those targets.
theorem later_arrival_is_not_first_old_start (s : State I T) (h : Exact s)
    (i : I) (t : T) (hi : s.initials i = true) (ht : s.targets t = true) :
    s.ready i t = true := registered_initial_is_ready s h i t hi ht

private theorem boolean_offer_order : ∀ old a b : Bool,
    ((old || a) || b) = ((old || b) || a) := by decide

theorem offer_order_pointwise (s : State I T)
    (a c : I → Bool) (b d : T → Bool) (h : Exact s) (i : I) (t : T) :
    (offer (offer s a b) c d).ready i t =
      (offer (offer s c d) a b).ready i t := by
  rw [offer_exact (offer s a b) c d (offer_exact s a b h) i t]
  rw [offer_exact (offer s c d) a b (offer_exact s c d h) i t]
  change (((s.initials i || a i) || c i) && ((s.targets t || b t) || d t)) =
    (((s.initials i || c i) || a i) && ((s.targets t || d t) || b t))
  rw [boolean_offer_order (s.initials i) (a i) (c i),
      boolean_offer_order (s.targets t) (b t) (d t)]

-- A route filter never drops a nonlocal or ZERO value. Local values use only
-- the given native mask. This theorem assumes no particular liveness solver.
inductive Kind where | nonlocal | zero | local deriving BEq, DecidableEq

def keep (kind : Kind) (live : Bool) : Bool :=
  match kind with
  | .nonlocal => true
  | .zero => true
  | .local => live

theorem nonlocal_all_routes (live : Bool) : keep .nonlocal live = true := by rfl
theorem zero_all_routes (live : Bool) : keep .zero live = true := by rfl
theorem local_filter_only (live : Bool) : keep .local live = live := by rfl

#print axioms empty_exact
#print axioms finite_offer_history_exact
#print axioms offer_exact
#print axioms registered_initial_is_ready
#print axioms complete_fanout
#print axioms later_arrival_is_not_first_old_start
#print axioms offer_order_pointwise
#print axioms nonlocal_all_routes
#print axioms zero_all_routes
#print axioms local_filter_only

end CanonicalNormalFanout
