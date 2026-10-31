import TerminalProtocol
import SelectedTargetApplication

/-! Constructive rooted ZERO settlement, derived from a finite admission route.
The assumptions are local: typed subscription readiness/matching, completed
delivery, complete NORMAL support, caller processing of received work, and the
previous committed snapshot invariant. No fresh child row is assumed reported.
The recursive witness walks earlier admission events to a configured root or a
previously reported retained row. The new committed invariant is then derived.
-/
namespace ZeroSettlement
open SelectedCore OwnedDelta TerminalProtocol SelectedTargetApplication
set_option autoImplicit false

abbrev Row := Key Premise
def zeroRow (owner id : Nat) : Row := ⟨owner,.zero,id⟩
def committedIds (roots previous : List Nat) (rows : List Row) : List Nat :=
  dedupReportIds (previous ++ rows.filterMap fun row =>
    if row.method ∈ roots ∧ row.premise = .zero then some row.id else none)

theorem previous_report_preserved (roots previous : List Nat) (rows : List Row)
    (id : Nat) (present : id ∈ previous) : id ∈ committedIds roots previous rows :=
  (dedup_report_membership _ _).mpr (List.mem_append.mpr (.inl present))
theorem root_row_collected (roots previous : List Nat) (rows : List Row) (owner id : Nat)
    (root : owner ∈ roots) (published : zeroRow owner id ∈ rows) :
    id ∈ committedIds roots previous rows := by
  apply (dedup_report_membership _ _).mpr
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_filterMap.mpr
  exact ⟨zeroRow owner id,published,if_pos ⟨root,rfl⟩⟩

structure ZeroHop (protocol : TerminalProtocol.State Premise)
    (matchRow : Subscription Premise → Row → Bool) where
  sub : Subscription Premise
  originalZero : sub.original = .zero
  prepared : sub ∈ protocol.ready
  support : Support
  admittedComplete : ready support = true
  allNormal : SelectedTargetApplication.allNormal support = true
  matchesZero : ∀ id, matchRow sub (zeroRow sub.callee id) = true

inductive FirstAdmissionRoute (roots : List Nat) (protocol : TerminalProtocol.State Premise)
    (matchRow : Subscription Premise → Row → Bool) : Nat → Nat → Type where
  | root (owner event : Nat) (configured : owner ∈ roots) :
      FirstAdmissionRoute roots protocol matchRow owner event
  | child {parentEvent childEvent : Nat} (hop : ZeroHop protocol matchRow)
      (earlier : parentEvent < childEvent)
      (parent : FirstAdmissionRoute roots protocol matchRow hop.sub.caller parentEvent) :
      FirstAdmissionRoute roots protocol matchRow hop.sub.callee childEvent

/-- Completed actor work: a valid NORMAL ZERO receipt is processed by the
    caller; exact-key suppression yields either retained or current membership.
    This is the Kotlin actor/fixed-point adapter, not a global report premise. -/
structure CompletedActor (retained : List Row) (protocol : TerminalProtocol.State Premise)
    (matchRow : Subscription Premise → Row → Bool) : Prop where
  receives : TerminalProtocol.Invariant matchRow protocol
  noPending : protocol.pending = []
  normalZeroReceipt : ∀ (hop : ZeroHop protocol matchRow) id,
    (hop.sub,zeroRow hop.sub.callee id) ∈ protocol.received →
    zeroRow hop.sub.caller id ∈ retained ∨ zeroRow hop.sub.caller id ∈ protocol.published

/-- Explicit selected caller work: a received NORMAL terminal offers exactly
    the caller's original complete premise and the same ReportId. -/
def receiptCandidate (delivery : Delivery Premise) : Row :=
  ⟨delivery.1.caller,delivery.1.original,delivery.2.id⟩
def processReceipts (initial : OwnedDelta.State Premise) (received : List (Delivery Premise)) : OwnedDelta.State Premise :=
  offerBatch initial (received.map receiptCandidate)

/-- Construct local receipt closure from the executable selected actor fold.
    `publishedAllSeen` is the completed required-publication boundary: no seen
    row is silently left unpublished. It is independent of final report IDs. -/
theorem completedActorFromProcessedReceipts (initial : OwnedDelta.State Premise)
    (protocol : TerminalProtocol.State Premise) (matchRow : Subscription Premise → Row → Bool)
    (invariant : TerminalProtocol.Invariant matchRow protocol) (complete : protocol.pending = [])
    (publishedAllSeen : ∀ row ∈ (processReceipts initial protocol.received).seen, row ∈ protocol.published) :
    CompletedActor initial.retained protocol matchRow where
  receives := invariant
  noPending := complete
  normalZeroReceipt := by
    intro hop id received
    have offered : receiptCandidate (hop.sub,zeroRow hop.sub.callee id) ∈ protocol.received.map receiptCandidate :=
      List.mem_map.mpr ⟨(hop.sub,zeroRow hop.sub.callee id),received,rfl⟩
    have held := batch_contains_every_offer initial _ _ offered
    change receiptCandidate (hop.sub,zeroRow hop.sub.callee id) ∈
      (processReceipts initial protocol.received).retained ++ (processReceipts initial protocol.received).seen at held
    have same : receiptCandidate (hop.sub,zeroRow hop.sub.callee id) = zeroRow hop.sub.caller id := by
      unfold receiptCandidate zeroRow
      rw [hop.originalZero]
    rw [same] at held
    rcases List.mem_append.mp held with retained | current
    · apply Or.inl
      simpa only [processReceipts,batch_retained_unchanged] using retained
    · exact .inr (publishedAllSeen _ current)

inductive Stop where
  | prior (method : Nat)
  | configuredRoot (method : Nat)
  deriving DecidableEq, Repr
structure Certificate (roots previous : List Nat) (retained : List Row)
    (protocol : TerminalProtocol.State Premise) (id : Nat) where
  stop : Stop
  stopValid : match stop with
    | .prior method => zeroRow method id ∈ retained ∧ id ∈ previous
    | .configuredRoot method => method ∈ roots ∧ zeroRow method id ∈ protocol.published
  reported : id ∈ committedIds roots previous protocol.published

/-- Executable route walk. It branches on exact retained membership and never
    chooses a root or report witness by an axiom. Recursion follows the finite
    earlier-event route even when the method call graph has recursion. -/
def settle (roots previous : List Nat) (retained : List Row)
    (protocol : TerminalProtocol.State Premise) (matchRow : Subscription Premise → Row → Bool)
    (prior : ∀ row ∈ retained, row.premise = .zero → row.id ∈ previous)
    (completed : CompletedActor retained protocol matchRow)
    {owner event : Nat} (route : FirstAdmissionRoute roots protocol matchRow owner event)
    (id : Nat) (held : zeroRow owner id ∈ retained ∨ zeroRow owner id ∈ protocol.published) :
    Certificate roots previous retained protocol id :=
  if saved : zeroRow owner id ∈ retained then
    let reported := prior (zeroRow owner id) saved rfl
    ⟨.prior owner,⟨saved,reported⟩,previous_report_preserved roots previous protocol.published id reported⟩
  else
    match route with
    | .root method _ configured =>
        let published := held.resolve_left saved
        ⟨.configuredRoot method,⟨configured,published⟩,
          root_row_collected roots previous protocol.published method id configured published⟩
    | .child hop _ parent =>
        let published := held.resolve_left saved
        let receipt := completed_receipt matchRow protocol completed.receives completed.noPending
          hop.sub hop.prepared (zeroRow hop.sub.callee id) published (hop.matchesZero id)
        settle roots previous retained protocol matchRow prior completed parent id
          (completed.normalZeroReceipt hop id receipt)

/-- The completed barrier derives the new ZERO report invariant from local
    processing plus supplied actual first-admission routes. It does not import
    a fresh-row ReplayCertificate that already assumes the desired result. -/
theorem committed_zero_invariant (roots previous : List Nat) (retained : List Row)
    (protocol : TerminalProtocol.State Premise) (matchRow : Subscription Premise → Row → Bool)
    (prior : ∀ row ∈ retained, row.premise = .zero → row.id ∈ previous)
    (completed : CompletedActor retained protocol matchRow)
    (routes : ∀ row ∈ protocol.published, row.premise = .zero →
      (event : Nat) × FirstAdmissionRoute roots protocol matchRow row.method event)
    (row : Row) (present : row ∈ retained ++ protocol.published) (isZero : row.premise = .zero) :
    row.id ∈ committedIds roots previous protocol.published := by
  rcases List.mem_append.mp present with saved | current
  · exact previous_report_preserved roots previous protocol.published row.id (prior row saved isZero)
  · cases row with
    | mk owner premise id =>
        cases isZero
        let route := routes (zeroRow owner id) current rfl
        exact (settle roots previous retained protocol matchRow prior completed route.2 id (.inr current)).reported

theorem skipped_committed_zero_adds_no_report (roots previous : List Nat) (retained : List Row)
    (protocol : TerminalProtocol.State Premise) (matchRow : Subscription Premise → Row → Bool)
    (prior : ∀ row ∈ retained, row.premise = .zero → row.id ∈ previous)
    (completed : CompletedActor retained protocol matchRow)
    {owner event : Nat} (route : FirstAdmissionRoute roots protocol matchRow owner event)
    (id : Nat) (held : zeroRow owner id ∈ retained ∨ zeroRow owner id ∈ protocol.published) :
    (if id ∈ committedIds roots previous protocol.published then committedIds roots previous protocol.published
      else id :: committedIds roots previous protocol.published) = committedIds roots previous protocol.published :=
  if_pos (settle roots previous retained protocol matchRow prior completed route id held).reported

structure Snapshot where
  rows : List Row
  reports : List Nat
  zeroReported : ∀ row ∈ rows, row.premise = .zero → row.id ∈ reports
def emptySnapshot : Snapshot := ⟨[],[],by intro _ absent; cases absent⟩

def readSavedNormal (snapshot : Snapshot) (direction : Direction) (row : Row)
    (caller : Nat) (callerOriginal : Premise) (support : Support) : Option Row :=
  match direction with
  | .backward => none
  | .forward =>
      if row ∈ snapshot.rows ∧ row.premise ≠ .zero ∧ ready support = true ∧
          SelectedTargetApplication.allNormal support = true then
        some ⟨caller,callerOriginal,row.id⟩ else none
theorem no_backward_saved_normal_application (snapshot : Snapshot) (row : Row)
    (caller : Nat) (original : Premise) (support : Support) :
    readSavedNormal snapshot .backward row caller original support = none := rfl
theorem no_settled_zero_saved_application (snapshot : Snapshot) (row : Row)
    (caller : Nat) (original : Premise) (support : Support) (zero : row.premise = .zero) :
    readSavedNormal snapshot .forward row caller original support = none :=
  if_neg (fun condition => condition.2.1 zero)
theorem settled_zero_cannot_add_report_id (snapshot : Snapshot) (row : Row)
    (saved : row ∈ snapshot.rows) (zero : row.premise = .zero) :
    (if row.id ∈ snapshot.reports then snapshot.reports else row.id :: snapshot.reports) = snapshot.reports :=
  if_pos (snapshot.zeroReported row saved zero)
theorem new_normal_caller_reads_saved_nonzero (snapshot : Snapshot) (row : Row)
    (caller : Nat) (original : Premise) (support : Support) (saved : row ∈ snapshot.rows)
    (nonzero : row.premise ≠ .zero) (admitted : ready support = true)
    (normal : SelectedTargetApplication.allNormal support = true) :
    readSavedNormal snapshot .forward row caller original support = some ⟨caller,original,row.id⟩ :=
  if_pos ⟨saved,nonzero,admitted,normal⟩

def completedSnapshot (roots : List Nat) (previous : Snapshot)
    (protocol : TerminalProtocol.State Premise) (matchRow : Subscription Premise → Row → Bool)
    (completed : CompletedActor previous.rows protocol matchRow)
    (routes : ∀ row ∈ protocol.published, row.premise = .zero →
      (event : Nat) × FirstAdmissionRoute roots protocol matchRow row.method event) : Snapshot :=
  ⟨previous.rows ++ protocol.published,committedIds roots previous.reports protocol.published,
    committed_zero_invariant roots previous.reports previous.rows protocol matchRow
      previous.zeroReported completed routes⟩

/-- A completed records/reports pair is exposed atomically; incomplete runs
    supply no new completed snapshot and therefore change neither component. -/
def expose (previous : Snapshot) : Option Snapshot → Snapshot
  | none => previous | some completed => completed
theorem incomplete_exposes_no_new_state (previous : Snapshot) : expose previous none = previous := rfl
theorem completed_report_ids_monotone (roots : List Nat) (previous : Snapshot)
    (protocol : TerminalProtocol.State Premise) (matchRow : Subscription Premise → Row → Bool)
    (completed : CompletedActor previous.rows protocol matchRow)
    (routes : ∀ row ∈ protocol.published, row.premise = .zero →
      (event : Nat) × FirstAdmissionRoute roots protocol matchRow row.method event)
    (id : Nat) (present : id ∈ previous.reports) :
    id ∈ (completedSnapshot roots previous protocol matchRow completed routes).reports :=
  previous_report_preserved roots previous.reports protocol.published id present

namespace Controls
def sub12 : Subscription Premise := ⟨12,2,1,.zero⟩
def sub01 : Subscription Premise := ⟨1,1,0,.zero⟩
def matchZero (sub : Subscription Premise) (row : Row) : Bool := sub.callee == row.method
def emptyProtocol : TerminalProtocol.State Premise := ⟨[],[],[],[],[],[]⟩
def prepared12 := prepare matchZero emptyProtocol sub12
def prepared01 := prepare matchZero prepared12 sub01
def childDelivered := drain (publish matchZero prepared01 (zeroRow 0 7))
def parentDelivered := drain (publish matchZero childDelivered (zeroRow 1 7))
def protocol := drain (publish matchZero parentDelivered (zeroRow 2 7))

theorem empty_valid : TerminalProtocol.Invariant matchZero emptyProtocol where
  readyRegistered := by intro _ member; cases member
  covered := by intro _ member; cases member
theorem protocol_valid : TerminalProtocol.Invariant matchZero protocol :=
  drain_preserves _ _ (publish_preserves _ _ _ (drain_preserves _ _
    (publish_preserves _ _ _ (drain_preserves _ _ (publish_preserves _ _ _
      (prepare_preserves _ _ _ (prepare_preserves _ _ _ empty_valid)))))))
def normalSupport : Support := ⟨true,true,[.normal],.normal⟩
def hop12 : ZeroHop protocol matchZero where
  sub := sub12
  originalZero := rfl
  prepared := by decide
  support := normalSupport
  admittedComplete := rfl
  allNormal := rfl
  matchesZero := fun _ => rfl
def hop01 : ZeroHop protocol matchZero where
  sub := sub01
  originalZero := rfl
  prepared := by decide
  support := normalSupport
  admittedComplete := rfl
  allNormal := rfl
  matchesZero := fun _ => rfl

theorem completed : CompletedActor [] protocol matchZero where
  receives := protocol_valid
  noPending := rfl
  normalZeroReceipt := by
    intro hop id received
    change (hop.sub,zeroRow hop.sub.callee id) ∈ [(sub12,zeroRow 1 7),(sub01,zeroRow 0 7)] at received
    rcases List.mem_cons.mp received with same | later
    · have callerEq := congrArg (fun pair : Subscription Premise × Row => pair.1.caller) same
      have idEq := congrArg (fun pair : Subscription Premise × Row => pair.2.id) same
      change hop.sub.caller = 2 at callerEq
      change id = 7 at idEq
      apply Or.inr
      change zeroRow hop.sub.caller id ∈ [zeroRow 2 7,zeroRow 1 7,zeroRow 0 7]
      rw [callerEq,idEq]
      decide
    · have same := List.mem_singleton.mp later
      have callerEq := congrArg (fun pair : Subscription Premise × Row => pair.1.caller) same
      have idEq := congrArg (fun pair : Subscription Premise × Row => pair.2.id) same
      change hop.sub.caller = 1 at callerEq
      change id = 7 at idEq
      apply Or.inr
      change zeroRow hop.sub.caller id ∈ [zeroRow 2 7,zeroRow 1 7,zeroRow 0 7]
      rw [callerEq,idEq]
      decide

def rootRoute : FirstAdmissionRoute [2] protocol matchZero 2 0 := .root 2 0 (by decide)
def parentRoute : FirstAdmissionRoute [2] protocol matchZero 1 1 := .child hop12 (by decide) rootRoute
def childRoute : FirstAdmissionRoute [2] protocol matchZero 0 2 := .child hop01 (by decide) parentRoute
def executableSettlement : Certificate [2] [] [] protocol 7 :=
  settle [2] [] [] protocol matchZero (by intro _ absent; cases absent) completed childRoute 7 (.inr (by decide))

theorem reports_nonroot_zero_via_normal_admission_route :
    7 ∈ committedIds [2] [] protocol.published := executableSettlement.reported
#eval executableSettlement.stop
end Controls

end ZeroSettlement
