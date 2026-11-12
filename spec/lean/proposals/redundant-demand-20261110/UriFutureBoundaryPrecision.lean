import Std

namespace UriFutureBoundaryPrecision
/- A selected native-table fragment, not a complete C2 model. It isolates
   the later-run STAR/FLOW cell and a one-field relative C5 cut. -/
inductive Tail where
  | exact | star | may
  deriving DecidableEq, Repr
inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr
structure Packet where
  path : List Nat
  tail : Tail
  layer : Layer
  deriving DecidableEq, Repr

def prefixB (p q : List Nat) : Bool := p == q.take p.length

def possible (packet : Packet) (word : List Nat) : Bool :=
  if packet.tail == .exact then packet.path == word else prefixB packet.path word

/- RestrictedInitialPolicy.emit, same-path / ancestor-MAY STAR demand cells.
   A deeper submitted path has no STAR admission after run-2. -/
def c2Star (demand : List Nat) (actual : Packet) : Option Packet :=
  if actual.path == demand then some ⟨demand,.exact,.normal⟩
  else if actual.tail == .may && prefixB actual.path demand then some ⟨demand,.exact,.normal⟩
  else none

def cut (budget : Nat) (packet : Packet) : Packet :=
  if packet.path.length > budget then ⟨packet.path.take budget,.may,.demand⟩ else packet

def content : Nat := 4
/- Two actual content-copy effects. The second current summary can be cut
   after its first-field initial, whereas a saved native copy replays raw. -/
def firstResult : Packet := ⟨[content],.exact,.normal⟩
def secondRaw : Packet := ⟨[content,content],.star,.normal⟩
def currentResult : Packet := cut 1 secondRaw
def savedResult : Packet := ⟨[content,content],.exact,.normal⟩
def requiredWord : List Nat := [content,content]
def consumerDemand : List Nat := [content]

theorem current_c5_is_may : currentResult = ⟨[content],.may,.demand⟩ := by decide
theorem current_contains_required_word : possible currentResult requiredWord = true := by decide
theorem saved_contains_required_word : possible savedResult requiredWord = true := by decide
theorem current_emits_exact_flow : c2Star consumerDemand currentResult = some ⟨[content],.exact,.normal⟩ := by decide
theorem saved_emits_no_current_initial : c2Star consumerDemand savedResult = none := by decide

def gate (packet : Packet) : Option Packet :=
  if (c2Star consumerDemand packet).isSome then some packet else none

theorem complete_empty_other_families_keep_current : gate currentResult = some currentResult := by decide
theorem complete_empty_other_families_drop_saved : gate savedResult = none := by decide

/- Containing the same genuine word is not enough to justify C2 monotonicity. -/
def wordCovered (source replacement : Packet) (word : List Nat) : Prop :=
  possible source word = true ∧ possible replacement word = true

theorem no_word_only_c2_lift :
    ¬ (∀ old new word, wordCovered old new word →
      (c2Star consumerDemand old).isSome = true → (c2Star consumerDemand new).isSome = true) := by
  intro purported
  have falseCell := purported currentResult savedResult requiredWord
    ⟨current_contains_required_word,saved_contains_required_word⟩ (by decide)
  contradiction

def readSaved (actual : Packet) : List Packet :=
  if prefixB [content] actual.path then
    [⟨actual.path.drop 1,actual.tail,actual.layer⟩]
  else []

/- A retained NORMAL reader is applied before C2. It supplies the required
   continuation even when the precise packet has no new current initial. -/
def boundary (actual : Packet) (hasSavedReader : Bool) : List Packet :=
  (if hasSavedReader then readSaved actual else []) ++
    (if (c2Star consumerDemand actual).isSome then [⟨[],.may,.demand⟩] else [])

theorem saved_reader_rescues_required_continuation :
    boundary savedResult true = [⟨[content],.exact,.normal⟩] := by decide

theorem absent_reader_exposes_the_c2_gap : boundary savedResult false = [] := by decide
end UriFutureBoundaryPrecision
#print axioms UriFutureBoundaryPrecision.current_c5_is_may
#print axioms UriFutureBoundaryPrecision.current_contains_required_word
#print axioms UriFutureBoundaryPrecision.saved_contains_required_word
#print axioms UriFutureBoundaryPrecision.current_emits_exact_flow
#print axioms UriFutureBoundaryPrecision.saved_emits_no_current_initial
#print axioms UriFutureBoundaryPrecision.complete_empty_other_families_keep_current
#print axioms UriFutureBoundaryPrecision.complete_empty_other_families_drop_saved
#print axioms UriFutureBoundaryPrecision.no_word_only_c2_lift
#print axioms UriFutureBoundaryPrecision.saved_reader_rescues_required_continuation
#print axioms UriFutureBoundaryPrecision.absent_reader_exposes_the_c2_gap
