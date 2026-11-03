import JoinedStateRelease
import LoopQueryReuse
import PackedStaticGuidance

namespace JoinedStateComposition

/- This module composes component ports. It does not model a new analyzer.
   ingest is the unchanged normalized, ordered source/bound-extra stream;
   admissions uses the same frozen exact scope/policy view; enclosingNative
   and enclosingPrepared are equal only under point 2's adapter obligations.
   Outcome/handoff/report functions consume complete values, not counts. -/

def referenceOracle (ingest : JoinedStateRelease.Retained → List PackedStaticGuidance.Row)
    (s : JoinedStateRelease.Session) : PackedStaticGuidance.Query → List PackedStaticGuidance.Row :=
  PackedStaticGuidance.oldOracle (ingest s.retained)

def selectedOracle (ingest : JoinedStateRelease.Retained → List PackedStaticGuidance.Row)
    (s : JoinedStateRelease.Session) : PackedStaticGuidance.Query → List PackedStaticGuidance.Row :=
  PackedStaticGuidance.newOracle
    (PackedStaticGuidance.compile (ingest (JoinedStateRelease.releaseExecution s).retained))

theorem release_preserves_complete_source_stream
    (ingest : JoinedStateRelease.Retained → List PackedStaticGuidance.Row)
    (s : JoinedStateRelease.Session) :
    ingest (JoinedStateRelease.releaseExecution s).retained = ingest s.retained := by
  rw [JoinedStateRelease.release_preserves_retained]

theorem release_and_packing_preserve_complete_oracle
    (ingest : JoinedStateRelease.Retained → List PackedStaticGuidance.Row)
    (s : JoinedStateRelease.Session) : selectedOracle ingest s = referenceOracle ingest s := by
  unfold selectedOracle referenceOracle
  rw [JoinedStateRelease.release_preserves_retained]
  exact PackedStaticGuidance.complete_oracle_equal (ingest s.retained)

def referenceObservation
    (admissions : K → Nat → List LoopQueryReuse.Admission)
    (adjacent repeats : K → List Nat)
    (enclosing : (PackedStaticGuidance.Query → List PackedStaticGuidance.Row) → K → List R)
    (oracle : PackedStaticGuidance.Query → List PackedStaticGuidance.Row) (key : K) :
    LoopQueryReuse.Observation R :=
  LoopQueryReuse.referenceObservation (admissions key) (adjacent key) (repeats key)
    (enclosing oracle key)

def selectedObservation
    (admissions : K → Nat → List LoopQueryReuse.Admission)
    (adjacent repeats : K → List Nat)
    (enclosing : (PackedStaticGuidance.Query → List PackedStaticGuidance.Row) → K → List R)
    (oracle : PackedStaticGuidance.Query → List PackedStaticGuidance.Row) (key : K) :
    LoopQueryReuse.Observation R :=
  LoopQueryReuse.bundledObservation (admissions key) (adjacent key) (repeats key)
    (enclosing oracle key)

theorem combined_complete_observer_port_equal
    (ingest : JoinedStateRelease.Retained → List PackedStaticGuidance.Row)
    (s : JoinedStateRelease.Session)
    (admissions : K → Nat → List LoopQueryReuse.Admission)
    (adjacent repeats : K → List Nat)
    (enclosingNative enclosingPrepared :
      (PackedStaticGuidance.Query → List PackedStaticGuidance.Row) → K → List R)
    (preparedPort : ∀ oracle key, enclosingPrepared oracle key = enclosingNative oracle key) :
    selectedObservation admissions adjacent repeats enclosingPrepared (selectedOracle ingest s) =
      referenceObservation admissions adjacent repeats enclosingNative (referenceOracle ingest s) := by
  funext key
  unfold selectedObservation referenceObservation
  rw [release_and_packing_preserve_complete_oracle ingest s, preparedPort]
  exact LoopQueryReuse.complete_three_family_signature_preserved
    (admissions key) (adjacent key) (repeats key)
    (enclosingNative (referenceOracle ingest s) key)

theorem combined_finite_restriction_program_equal [DecidableEq K]
    (ingest : JoinedStateRelease.Retained → List PackedStaticGuidance.Row)
    (s : JoinedStateRelease.Session)
    (admissions : K → Nat → List LoopQueryReuse.Admission)
    (adjacent repeats : K → List Nat)
    (enclosingNative enclosingPrepared :
      (PackedStaticGuidance.Query → List PackedStaticGuidance.Row) → K → List R)
    (preparedPort : ∀ oracle key, enclosingPrepared oracle key = enclosingNative oracle key)
    (capacity : Nat) (program : LoopQueryReuse.Program K (LoopQueryReuse.Observation R) O) :
    LoopQueryReuse.ownerQuantum
      (selectedObservation admissions adjacent repeats enclosingPrepared (selectedOracle ingest s))
      capacity program =
    LoopQueryReuse.evaluate
      (referenceObservation admissions adjacent repeats enclosingNative (referenceOracle ingest s)) program := by
  rw [combined_complete_observer_port_equal ingest s admissions adjacent repeats
    enclosingNative enclosingPrepared preparedPort]
  exact LoopQueryReuse.cache_dies_with_quantum _ capacity program

theorem combined_handoff_and_report_projection_equal [DecidableEq K]
    (ingest : JoinedStateRelease.Retained → List PackedStaticGuidance.Row)
    (s : JoinedStateRelease.Session)
    (admissions : K → Nat → List LoopQueryReuse.Admission)
    (adjacent repeats : K → List Nat)
    (enclosingNative enclosingPrepared :
      (PackedStaticGuidance.Query → List PackedStaticGuidance.Row) → K → List R)
    (preparedPort : ∀ oracle key, enclosingPrepared oracle key = enclosingNative oracle key)
    (capacity : Nat) (program : LoopQueryReuse.Program K (LoopQueryReuse.Observation R) O)
    (handoff : JoinedStateRelease.Exports → O → H) (observeReport : H → T) :
    observeReport (handoff (JoinedStateRelease.releaseExecution s).retained.exports
      (LoopQueryReuse.ownerQuantum
        (selectedObservation admissions adjacent repeats enclosingPrepared (selectedOracle ingest s))
        capacity program)) =
    observeReport (handoff s.retained.exports
      (LoopQueryReuse.evaluate
        (referenceObservation admissions adjacent repeats enclosingNative (referenceOracle ingest s)) program)) := by
  rw [JoinedStateRelease.release_preserves_retained]
  rw [combined_finite_restriction_program_equal ingest s admissions adjacent repeats
    enclosingNative enclosingPrepared preparedPort capacity program]

theorem combined_static_callback_trace_equal
    (ingest : JoinedStateRelease.Retained → List PackedStaticGuidance.Row)
    (s : JoinedStateRelease.Session) (ids : List Nat) (keep : PackedStaticGuidance.Row → Bool)
    (step : S → PackedStaticGuidance.Row → S × Bool) (start : S) :
    PackedStaticGuidance.visitUntil step start
      (PackedStaticGuidance.catalogQuery
        (PackedStaticGuidance.compile (ingest (JoinedStateRelease.releaseExecution s).retained)) ids keep) =
    PackedStaticGuidance.visitUntil step start
      (PackedStaticGuidance.query (ingest s.retained) ids keep) := by
  rw [JoinedStateRelease.release_preserves_retained]
  exact PackedStaticGuidance.callback_trace_equal (ingest s.retained) ids keep step start

theorem NORMAL_and_DEMAND_Target_export_ids_equal (s : JoinedStateRelease.Session) :
    (JoinedStateRelease.releaseExecution s).retained.exports.rawTargets =
      s.retained.exports.rawTargets ∧
    (JoinedStateRelease.releaseExecution s).retained.exports.outgoingDemandTargets =
      s.retained.exports.outgoingDemandTargets := by
  rw [JoinedStateRelease.release_preserves_retained]
  exact ⟨rfl, rfl⟩

theorem packed_oracle_preserves_finite_recursive_compositions
    (ingest : JoinedStateRelease.Retained → List PackedStaticGuidance.Row)
    (s : JoinedStateRelease.Session) (ask : S → PackedStaticGuidance.Query)
    (advance : S → List PackedStaticGuidance.Row → S) (steps : Nat) (start : S) :
    PackedStaticGuidance.iterate (selectedOracle ingest s) ask advance steps start =
      PackedStaticGuidance.iterate (referenceOracle ingest s) ask advance steps start := by
  rw [release_and_packing_preserve_complete_oracle ingest s]

end JoinedStateComposition
