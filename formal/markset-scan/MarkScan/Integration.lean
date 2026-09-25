import MarkScan.EngineSoundness
import MarkScan.Selection
import MarkScan.Coarsening

/-!
# End-to-end exactness of the mark-set selection

Composes engine soundness (`EngineSoundness`), selection and relevance
exactness (`Selection`), and node coarsening with statement keying
(`Coarsening`) into the contract the runner relies on.
-/
namespace MarkScan

/-- The restricted full scan reports exactly the baseline findings when the
installed selection over-approximates `Applicable` and `Needed` of the
recorded program. -/
theorem markset_exact {p : Program} (wf : PcWF p)
    {app : Node → Pc → ESite → Bool} {need : Mark → Bool}
    (hAppB : ∀ n pc σ, Applicable p n pc σ → app n pc σ = true)
    (hNeed : ∀ m, Needed p m → need m = true)
    {n : Node} {pc : Pc} {σ : ESite} :
    Fires p Sel.all n pc σ ↔ Fires p (Sel.ofScan app need) n pc σ :=
  rel_fires_iff (fun _ _ _ _ hs hc hh => ecube_applicable wf hs hc hh) hAppB hNeed

/-- The implemented configuration. The scan runs on the context-merged graph
`q`, and its applicability is keyed by statement. The resulting selection,
pulled back to the fine per-context program `p` that the engine runs, still
reports exactly the baseline findings. -/
theorem markset_exact_coarse {p q : Program} (wf : PcWF p)
    {h : Node → Node} {hp : Pc → Pc} (H : Hom p q h hp)
    {stmtOf : Node → Pc → Nat} {appK : Nat → ESite → Bool} {need : Mark → Bool}
    (hK : ∀ s σ, stmtApplicable q stmtOf s σ → appK s σ = true)
    (hN : ∀ m, Needed q m → need m = true)
    {n : Node} {pc : Pc} {σ : ESite} :
    Fires p Sel.all n pc σ ↔
      Fires p (Sel.ofScan (fun n pc σ => appK (stmtOf (h n) (hp pc)) σ) need) n pc σ :=
  markset_exact wf (coarse_keyed_overapprox H hK) (coarse_needed_overapprox H hN)

/-! ## Axiom audit
Run `./check.sh`: `AxiomAudit.lean` prints the axioms of every theorem. -/

end MarkScan
