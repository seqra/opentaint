import Std

/- Constructive component model for the post-main JVM adapter. Field IDs are
   already typed and interned. No claim is made about the native analyzer or
   all-program convergence. No legacy request/deepening engine is modeled. -/
namespace MainMigration
set_option autoImplicit false

structure Pos where
  base : Nat
  path : List Nat
  deriving DecidableEq, BEq, Repr

inductive Modifier where
  | field (id : Nat)
  | any
  deriving DecidableEq, BEq, Repr

def split : List Modifier → List Nat × Bool
  | [] => ([], false)
  | .any :: _ => ([], true)
  | .field f :: rest => let tail := split rest; (f :: tail.1, tail.2)

structure Desc where
  pos : Pos
  any : Bool
  deriving DecidableEq, BEq, Repr

def bind (base : Nat) (mods : List Modifier) : Desc :=
  let result := split mods
  ⟨⟨base,result.1⟩,result.2⟩

def encode (d : Desc) : List Modifier :=
  d.pos.path.map Modifier.field ++ if d.any then [.any] else []

theorem split_concrete (path : List Nat) :
    split (path.map Modifier.field) = (path,false) := by
  induction path with
  | nil => rfl
  | cons f rest ih => simp [split,ih]

theorem first_any_discards_only_the_suffix (path : List Nat) (rest : List Modifier) :
    split (path.map Modifier.field ++ .any :: rest) = (path,true) := by
  induction path with
  | nil => rfl
  | cons f tail ih => simp [split,ih]

theorem canonical_position_roundtrip (d : Desc) :
    bind d.pos.base (encode d) = d := by
  rcases d with ⟨⟨base,path⟩,any⟩
  cases any <;> simp [bind,encode,split_concrete,first_any_discards_only_the_suffix]

theorem concrete_prefix_is_not_changed (base : Nat) (path : List Nat) :
    bind base (path.map Modifier.field) = ⟨⟨base,path⟩,false⟩ := by
  simp [bind,split_concrete]

theorem trailing_any_is_not_a_concrete_field (base : Nat) (path : List Nat) :
    bind base (path.map Modifier.field ++ [.any]) = ⟨⟨base,path⟩,true⟩ := by
  simp [bind,first_any_discards_only_the_suffix]

def pathPrefix : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: rest, b :: tail => a == b && pathPrefix rest tail

def region (head value : Pos) : Bool :=
  head.base == value.base && pathPrefix head.path value.path

def selector (d : Desc) (value : Pos) : Bool :=
  if d.any then region d.pos value else d.pos == value

theorem path_prefix_reflexive (path : List Nat) : pathPrefix path path = true := by
  induction path with
  | nil => rfl
  | cons f rest ih =>
      have same : (f == f) = true := by
        change decide (f = f) = true
        exact decide_eq_true rfl
      simp only [pathPrefix,same,Bool.true_and,ih]

theorem region_includes_its_head (p : Pos) : region p p = true := by
  have same : (p.base == p.base) = true := by
    change decide (p.base = p.base) = true
    exact decide_eq_true rfl
  simp only [region,same,path_prefix_reflexive,Bool.true_and]

def starCheck (p : Pos) (value : Pos) : Bool :=
  selector ⟨p,false⟩ value || selector ⟨p,true⟩ value

theorem plain_check_implies_star (p value : Pos) (hit : (p == value) = true) :
    starCheck p value = true := by
  simp [starCheck,selector,hit]

theorem plain_and_star_is_plain (p value : Pos) :
    (selector ⟨p,false⟩ value && starCheck p value) = selector ⟨p,false⟩ value := by
  simp only [starCheck]
  cases selector ⟨p,false⟩ value <;> simp

theorem plain_and_not_star_is_false (p value : Pos) :
    (selector ⟨p,false⟩ value && !(starCheck p value)) = false := by
  simp only [starCheck]
  cases selector ⟨p,false⟩ value <;> simp

inductive Condition where
  | truth (value : Bool)
  | cm (pos : Desc) (mark : Nat)
  | neg (child : Condition)
  | conj (left right : Condition)
  | disj (left right : Condition)
  deriving DecidableEq, Repr

structure Marked where
  pos : Pos
  mark : Nat
  deriving DecidableEq, BEq, Repr

inductive Atom where
  | exact (pos : Pos) (mark : Nat)
  | any (pos : Pos) (mark : Nat)
  deriving DecidableEq, Repr

inductive Predicate where
  | truth (value : Bool)
  | leaf (atom : Atom)
  | neg (child : Predicate)
  | conj (left right : Predicate)
  | disj (left right : Predicate)
  deriving DecidableEq, Repr

def observe (facts : List Marked) (d : Desc) (mark : Nat) : Bool :=
  facts.any (fun fact => fact.mark == mark && selector d fact.pos)

def eval (facts : List Marked) : Condition → Bool
  | .truth value => value
  | .cm d mark => observe facts d mark
  | .neg child => !(eval facts child)
  | .conj left right => eval facts left && eval facts right
  | .disj left right => eval facts left || eval facts right

def lower : Condition → Predicate
  | .truth value => .truth value
  | .cm d mark => .leaf (if d.any then .any d.pos mark else .exact d.pos mark)
  | .neg child => .neg (lower child)
  | .conj left right => .conj (lower left) (lower right)
  | .disj left right => .disj (lower left) (lower right)

def atomEval (facts : List Marked) : Atom → Bool
  | .exact pos mark => facts.any (fun fact => fact.mark == mark && pos == fact.pos)
  | .any pos mark => facts.any (fun fact => fact.mark == mark && region pos fact.pos)

def predEval (facts : List Marked) : Predicate → Bool
  | .truth value => value
  | .leaf atom => atomEval facts atom
  | .neg child => !(predEval facts child)
  | .conj left right => predEval facts left && predEval facts right
  | .disj left right => predEval facts left || predEval facts right

theorem condition_lowering_preserves_truth (facts : List Marked) (c : Condition) :
    predEval facts (lower c) = eval facts c := by
  induction c with
  | truth value => rfl
  | cm d mark => cases flag : d.any <;> simp [lower,predEval,atomEval,eval,observe,selector,flag]
  | neg child ih => simp [lower,predEval,eval,ih]
  | conj left right il ir => simp [lower,predEval,eval,il,ir]
  | disj left right il ir => simp [lower,predEval,eval,il,ir]

theorem complete_and_guard_is_retained (facts : List Marked) (a b : Condition) :
    predEval facts (lower (.conj a b)) = (eval facts a && eval facts b) := by
  simp [condition_lowering_preserves_truth,eval]

theorem explicit_star_uses_or (facts : List Marked) (p : Pos) (mark : Nat) :
    predEval facts (lower (.disj (.cm ⟨p,false⟩ mark) (.cm ⟨p,true⟩ mark))) =
      (observe facts ⟨p,false⟩ mark || observe facts ⟨p,true⟩ mark) := by
  simp [condition_lowering_preserves_truth,eval]

inductive Tail where | exact | star | may | must deriving DecidableEq, BEq, Repr
inductive Layer where | normal | demand deriving DecidableEq, BEq, Repr

structure Pattern where
  pos : Pos
  tail : Tail
  mark : Nat
  deriving DecidableEq, BEq, Repr

def sourceTarget (d : Desc) (mark : Nat) : Pattern :=
  ⟨d.pos,if d.any then .must else .exact,mark⟩

def passTarget (d : Desc) (mark : Nat) : Pattern :=
  ⟨d.pos,if d.any then .may else .star,mark⟩

def patternCovers (pattern : Pattern) (fact : Marked) : Bool :=
  pattern.mark == fact.mark &&
    match pattern.tail with
    | .exact => pattern.pos == fact.pos
    | .star | .may | .must => region pattern.pos fact.pos

theorem ordinary_source_is_exact (p : Pos) (mark : Nat) :
    sourceTarget ⟨p,false⟩ mark = ⟨p,.exact,mark⟩ := rfl

theorem any_source_is_uniform (p : Pos) (mark : Nat) :
    sourceTarget ⟨p,true⟩ mark = ⟨p,.must,mark⟩ := rfl

theorem source_and_pass_any_targets_are_distinct (p : Pos) (mark : Nat) :
    (sourceTarget ⟨p,true⟩ mark).tail ≠ (passTarget ⟨p,true⟩ mark).tail := by simp [sourceTarget,passTarget]

theorem source_target_covers_exactly_its_declared_region (d : Desc) (mark : Nat) (value : Marked) :
    patternCovers (sourceTarget d mark) value =
      (mark == value.mark && selector d value.pos) := by
  cases flag : d.any <;> simp [patternCovers,sourceTarget,selector,flag]

structure Stamp where
  owner : Nat
  ruleOrdinal : Nat
  actionOrdinal : Nat
  deriving DecidableEq, BEq, Repr

structure SourceAction where
  stamp : Stamp
  target : Desc
  mark : Nat
  deriving DecidableEq, BEq, Repr

structure BoundSource where
  stamp : Stamp
  target : Pattern
  deriving DecidableEq, BEq, Repr

def bindSource (action : SourceAction) : BoundSource :=
  ⟨action.stamp,sourceTarget action.target action.mark⟩

theorem source_identity_is_preserved (action : SourceAction) :
    (bindSource action).stamp = action.stamp := rfl

theorem source_vector_keeps_order_and_duplicates (actions : List SourceAction) :
    (actions.map bindSource).map BoundSource.stamp = actions.map SourceAction.stamp := by
  simp [List.map_map,Function.comp_def,bindSource]

structure Payload where
  premise : Pattern
  conclusion : Pattern
  layer : Layer
  excludedFields : List Nat
  excludedMarks : List Nat
  isProtected : Bool
  deriving DecidableEq, BEq, Repr

def routePass (geometry : Pattern → Pattern) (edge : Payload) : Payload :=
  {edge with conclusion := geometry edge.conclusion}

theorem pass_preserves_all_support_headers (geometry : Pattern → Pattern) (edge : Payload) :
    (routePass geometry edge).premise = edge.premise ∧
    (routePass geometry edge).layer = edge.layer ∧
    (routePass geometry edge).excludedFields = edge.excludedFields ∧
    (routePass geometry edge).excludedMarks = edge.excludedMarks ∧
    (routePass geometry edge).isProtected = edge.isProtected := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem pass_cannot_create_protection (geometry : Pattern → Pattern) (edge : Payload)
    (plain : edge.isProtected = false) :
    (routePass geometry edge).isProtected = false := plain

theorem opposite_protection_classes_are_distinct (edge : Payload) :
    {edge with isProtected := false} ≠ {edge with isProtected := true} := by
  intro eq
  have impossible := congrArg Payload.isProtected eq
  contradiction

inductive Shape where
  | source (target : Desc)
  | pass (input output : Desc)
  | removeSelected (target : Desc)
  | removeAll (target : Desc)
  deriving DecidableEq, Repr

def allowed : Shape → Bool
  | .source _ => true
  | .pass input _ => !input.any
  | .removeSelected _ => true
  | .removeAll target => !target.any

theorem any_pass_premise_stays_rejected (p : Pos) (to : Desc) :
    allowed (.pass ⟨p,true⟩ to) = false := rfl

theorem below_only_removeAll_stays_rejected (p : Pos) :
    allowed (.removeAll ⟨p,true⟩) = false := rfl

inductive CleanReach where | exact | below | atAndBelow deriving DecidableEq, Repr

def selectedCleanReach (target : Desc) : CleanReach :=
  if target.any then .below else .exact

/- The existing source-definition reset is NOT the selected cleaner action.
   A uniform source owns the prefix too. Keep that reset on its old core
   primitive instead of encoding it through the removed rule reach field. -/
def returnResetReach (source : Bool) (target : Desc) : CleanReach :=
  if target.any then (if source then .atAndBelow else .below) else .exact

theorem any_selected_clean_keeps_below_scope (p : Pos) :
    selectedCleanReach ⟨p,true⟩ = .below := rfl

theorem any_source_definition_reset_keeps_whole_scope (p : Pos) :
    returnResetReach true ⟨p,true⟩ = .atAndBelow := rfl

theorem cleaner_definition_reset_preserves_selected_reach (target : Desc) :
    returnResetReach false target = selectedCleanReach target := by
  cases flag : target.any <;> simp [returnResetReach,selectedCleanReach,flag]

def choosePass (explicit fallback : List Nat) : List Nat :=
  if explicit.isEmpty then fallback else explicit

theorem fallback_when_no_explicit_rule (fallback : List Nat) :
    choosePass [] fallback = fallback := rfl

theorem no_fallback_after_present_rule (head : Nat) (rest fallback : List Nat) :
    choosePass (head :: rest) fallback = head :: rest := rfl

theorem rejected_outputs_do_not_enable_fallback (rule : Nat) (fallback : List Nat)
    (accept : Nat → Bool) (reject : accept rule = false) :
    (choosePass [rule] fallback).filter accept = [] := by
  simp [choosePass,reject]

structure Binding where
  metavar : Nat
  pos : Pos
  deriving DecidableEq, BEq, Repr

def focusSelected (focus : List Nat) (binding : Binding) : Bool :=
  focus.isEmpty || focus.contains binding.metavar

def cleanerTargets (defaults : List Pos) (focus : List Nat) (bindings : List Binding) : List Pos :=
  defaults ++ (bindings.filter (focusSelected focus)).map Binding.pos

theorem nonfocus_binding_is_not_added (focus : List Nat) (binding : Binding)
    (reject : focusSelected focus binding = false) :
    cleanerTargets [] focus [binding] = [] := by
  simp [cleanerTargets,reject]

theorem selected_binding_is_added (defaults : List Pos) (focus : List Nat) (binding : Binding)
    (accept : focusSelected focus binding = true) :
    cleanerTargets defaults focus [binding] = defaults ++ [binding.pos] := by
  simp [cleanerTargets,accept]

theorem focus_free_keeps_all_matched_positions (defaults : List Pos) (bindings : List Binding) :
    cleanerTargets defaults [] bindings = defaults ++ bindings.map Binding.pos := by
  have keep : bindings.filter (focusSelected []) = bindings :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [cleanerTargets,keep]

def cleanExact (p : Pos) (mark : Nat) (facts : List Marked) : List Marked :=
  facts.filter (fun fact => !(fact.mark == mark && p == fact.pos))

theorem exact_clean_has_no_implicit_child_effect (p child : Pos) (mark : Nat)
    (different : (p == child) = false) :
    cleanExact p mark [⟨child,mark⟩] = [⟨child,mark⟩] := by
  simp only [cleanExact,List.filter_cons,List.filter_nil,different,
    Bool.and_false,Bool.not_false,ite_true]

structure Config where
  schedule : List Nat
  legacyCap : Option Nat
  deriving DecidableEq, Repr

structure EffectiveConfig where
  schedule : List Nat
  diagnostics : List String
  deriving DecidableEq, Repr

def bidiConfig (c : Config) : EffectiveConfig :=
  ⟨c.schedule,match c.legacyCap with
    | none => []
    | some _ => ["iteration-limit is ignored by the bidirectional engine"]⟩

theorem legacy_cap_never_changes_bidi_schedule (schedule : List Nat) (cap : Option Nat) :
    (bidiConfig ⟨schedule,cap⟩).schedule = schedule := rfl

theorem explicit_cap_produces_one_diagnostic (schedule : List Nat) (cap : Nat) :
    (bidiConfig ⟨schedule,some cap⟩).diagnostics.length = 1 := rfl

theorem absent_cap_is_silent (schedule : List Nat) :
    (bidiConfig ⟨schedule,none⟩).diagnostics = [] := rfl

/- Models the provider's legacy Z2F gate and its explicit controller bypass.
   It does not model annotations or a sink evaluator. -/
def exitRuleVisible (generated controller initialFactsPresent : Bool) : Bool :=
  !generated && (controller || !initialFactsPresent)

theorem controller_exit_does_not_require_ZERO (present : Bool) :
    exitRuleVisible false true present = true := by simp [exitRuleVisible]

theorem generated_exit_rules_stay_hidden (controller present : Bool) :
    exitRuleVisible true controller present = false := rfl

def analyzeBody (completePredefined : Bool) : Bool := !completePredefined

theorem complete_predefined_does_not_add_body_analysis : analyzeBody true = false := rfl

namespace Examples
def x : Pos := ⟨1,[]⟩
def xf : Pos := ⟨1,[10]⟩
def xg : Pos := ⟨1,[20]⟩
def ret : Pos := ⟨2,[]⟩

theorem E01_plain_array_check_has_no_implicit_element :
    observe [⟨xf,7⟩] ⟨x,false⟩ 7 = false ∧
    observe [⟨xf,7⟩] ⟨x,true⟩ 7 = true := by decide

theorem E02_starred_field_only_exclusion_is_satisfiable :
    starCheck x xf = true ∧ selector ⟨x,false⟩ xf = false := by decide

theorem E03_distinct_AND_inputs_are_not_OR :
    eval [⟨xf,7⟩] (.conj (.cm ⟨xf,false⟩ 7) (.cm ⟨xg,false⟩ 8)) = false := by decide

theorem E04_main_normalization_retains_the_prefix :
    bind 1 [.field 10,.any,.field 20] = ⟨xf,true⟩ := by decide

theorem E05_accessor_focus_does_not_clean_receiver :
    cleanerTargets [ret] [7] [⟨7,ret⟩,⟨8,x⟩] = [ret,ret] := by decide

theorem E06_pass_sanitizer_keeps_its_focused_argument :
    cleanerTargets [ret] [7] [⟨7,x⟩] = [ret,x] := by decide

theorem E07_no_focus_keeps_the_receiver_policy :
    cleanerTargets [ret] [] [⟨7,ret⟩,⟨8,x⟩] = [ret,ret,x] := by decide

theorem E08_named_model_fields_are_not_interchangeable :
    selector ⟨xf,false⟩ xg = false := by decide

theorem E09_explicit_cap_zero_keeps_run1_limit_one :
    bidiConfig ⟨[1,1,2,3],some 0⟩ =
      ⟨[1,1,2,3],["iteration-limit is ignored by the bidirectional engine"]⟩ := by decide

theorem E10_ANY_source_and_pass_do_not_share_the_tail :
    sourceTarget ⟨xf,true⟩ 7 = ⟨xf,.must,7⟩ ∧
    passTarget ⟨xf,true⟩ 7 = ⟨xf,.may,7⟩ := by decide

theorem E11_exact_clean_does_not_clean_string_bytes :
    cleanExact x 7 [⟨x,7⟩,⟨xf,7⟩] = [⟨xf,7⟩] := by decide
end Examples
end MainMigration
