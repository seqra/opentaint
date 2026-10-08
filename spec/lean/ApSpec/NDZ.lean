/-
  ApSpec.NDZ — the ND closure of the spec: a conjunction and an ND summary application JOIN the
  premise lists WITHOUT THE ZERO FACT (spec §4.6, analyzer-core.md §5.4). `ND.DN` keeps the zero
  fact in the joined list (the model of the support semantics); `DNz` drops it. This file holds
  the definitions only; `NDZero.lean` proves the correspondence `DN` ↔ `DNz` and the theorems of
  `DNz`.

  * `zStar`: the zero binding `zero.* → zero.*` of a call (spec §3.5).
  * `dropZ P`: `P` without the zero fact; `[zeroFact]` if nothing is left. So `{zero} ∪ {i} = {i}` and
    `{zero} ∪ {zero} = {zero}`.
  * `DNz`: the rules of `ND.DN`, with `dropZ` at `conj` and `ndRet`.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.ND

namespace ApSpec.NDZ
open ApSpec ApSpec.ND

/-- The zero binding of a call: `zero.* → zero.*` (spec §3.5). -/
def zStar : PFact := ⟨zeroBase, [], .star Excl.empty, .star⟩

/-- A premise list without the zero fact; `[zeroFact]` if nothing is left (spec §4.6). -/
def dropZ (P : List PFact) : List PFact :=
  match P.filter (fun i => i != zeroFact) with
  | [] => [zeroFact]
  | L => L

/-- The ND closure of the spec: `ND.DN` with the zero-drop at `conj` and `ndRet`. -/
inductive DNz (X : Ctx) : NObj → Prop where
  | root {M} : M ∈ X.roots → DNz X (.ninit M zeroFact)
  | start {M i} : DNz X (.ninit M i) → DNz X (.nedge M [i] (X.Q.prog.entry M) (startFact i))
  | step {M P n f n' s f'} :
      DNz X (.nedge M P n f) → (M, n, Instr.stmt s, n') ∈ X.Q.prog.edges →
      f' ∈ (transfer X.counted X.FL s f).facts → DNz X (.nedge M P n' f')
  | reqStmt {M i n f n' s t} :
      DNz X (.nedge M [i] n f) → (M, n, Instr.stmt s, n') ∈ X.Q.prog.edges →
      t ∈ (transfer X.counted X.FL s f).reqs → DNz X (.nreq M i t)
  | pass {M P n f n' c} :
      DNz X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      memB f.fact.base c.touched = false → DNz X (.nedge M P n' f)
  | added {M P n f n' c e a} :
      DNz X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts → DNz X (.nadded c.callee a.fact)
  | initA {m a} : DNz X (.nadded m a) → DNz X (.ninit m (X.α m a))
  -- a single-premise callee summary keeps the premise list of the caller edge
  | ret {M P n f n' c e1 a j g r e2 r'} :
      DNz X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DNz X (.ninit c.callee j) → applicable j a.fact = true →
      DNz X (.nedge c.callee [j] (X.Q.prog.exit c.callee) g) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DNz X (.nedge M P n' (limitF X.counted X.FL r'))
  -- an ND callee summary (two or more premises) opens a standing partial match at a call
  | ndOpen {M n c n' Pc g} :
      (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      DNz X (.nedge c.callee Pc (X.Q.prog.exit c.callee) g) → 2 ≤ Pc.length →
      DNz X (.npart M n c n' Pc [] g)
  -- one caller edge whose binding satisfies the next callee premise; its layer joins the
  -- layer of the partial match (the result is demand if a caller edge or the summary is)
  | ndBind {M n c n' p ps P g Pf f e1 a} :
      DNz X (.npart M n c n' (p :: ps) P g) → DNz X (.nedge M Pf n f) →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts → applicable p a.fact = true →
      DNz X (.npart M n c n' ps (P ++ Pf) ⟨g.fact, g.demand || a.demand⟩)
  -- every callee premise is matched: the conclusion is used as it is (no delta), bound back; the joined caller
  -- premise lists drop the zero fact (spec §4.6)
  | ndRet {M n c n' P g e2 r} :
      DNz X (.npart M n c n' [] P g) → e2 ∈ c.fromCallee →
      r ∈ (applyEdge g e2.1 e2.2).facts → DNz X (.nedge M (dropZ P) n' (limitF X.counted X.FL r))
  | reqSink {M i n f s t} :
      DNz X (.nedge M [i] n f) → (M, n, s) ∈ X.sinks → check i f s = .request t →
      DNz X (.nreq M i t)
  | answer {M i t a} :
      DNz X (.nreq M i t) → DNz X (.nadded M a) → a.mark = .conc t →
      overlapB a i = true → DNz X (.ninit M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      DNz X (.nreq m j t) → DNz X (.nedge M [ic] n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → DNz X (.nreq M ic t)
  -- the sink check reads the mark of a premise only for a mark-abstract conclusion; an ND
  -- conclusion has a concrete mark, so the choice of the premise does not matter
  | vuln {M P n f s i} :
      DNz X (.nedge M P n f) → (M, n, s) ∈ X.sinks → i ∈ P → check i f s = .triggered →
      DNz X (.nvuln M n s f.demand)
  | clean {M P n f n' cl f'} :
      DNz X (.nedge M P n f) → (M, n, Instr.clean cl, n') ∈ X.Q.prog.edges →
      f' ∈ (cleanRes cl f).facts → DNz X (.nedge M P n' f')
  | reqClean {M i n f n' cl t} :
      DNz X (.nedge M [i] n f) → (M, n, Instr.clean cl, n') ∈ X.Q.prog.edges →
      t ∈ (cleanRes cl f).reqs → DNz X (.nreq M i t)
  | filt {M P n f n' b may} :
      DNz X (.nedge M P n f) → (M, n, Instr.filt b may, n') ∈ X.Q.prog.edges →
      (f.fact.base = b → may f.fact.path = true) → DNz X (.nedge M P n' f)
  -- the conjunction: one edge per literal; the premise lists are joined WITHOUT the zero fact (spec §4.6)
  | conj {M P1 n f1 P2 f2 cj n'} :
      DNz X (.nedge M P1 n f1) → DNz X (.nedge M P2 n f2) → (M, n, cj, n') ∈ X.Q.conjs →
      overlapB f1.fact cj.lit1 = true → markGate cj.lit1.mark f1.fact.mark = .ok →
      overlapB f2.fact cj.lit2 = true → markGate cj.lit2.mark f2.fact.mark = .ok →
      DNz X (.nedge M (dropZ (P1 ++ P2)) n' (conjFact cj f1 f2))
  -- a literal on a mark-abstract fact raises the request of the literal mark (run 1)
  | reqConj {M i n f cj n' lit t} :
      DNz X (.nedge M [i] n f) → (M, n, cj, n') ∈ X.Q.conjs → (lit = cj.lit1 ∨ lit = cj.lit2) →
      overlapB f.fact lit = true → markGate lit.mark f.fact.mark = .req t → DNz X (.nreq M i t)

end ApSpec.NDZ
