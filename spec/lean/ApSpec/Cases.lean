/-
  ApSpec.Cases — the cases of bidirectional-task.md as executable test vectors.

  Each `example` is checked by `decide` (kernel evaluation, no extra axiom).
  The same vectors are the reference for the Kotlin unit tests (spec §13).

  Round 5 (namespace `ApSpec.CleanCases`, at the end): the cleaner with a mark exclusion
  (`cleanRes`, `markComp`, `check`, `markGate`, `climbsB` on `*∖x`) and the type filter
  (`filt`, prefix-closed predicate on the first accessor).
-/
import ApSpec.Basic

namespace ApSpec.Cases
open ApSpec

-- accessors
def f : Acc := 1
def g : Acc := 2
def h : Acc := 3
-- bases
def x : Base := 10
def a : Base := 11
def b : Base := 12
-- marks
def T : Mark := 5

def allCounted : Acc → Bool := fun _ => true

def star (e : Excl) : Kind := .star e
def E1 : Excl := .set [h]

def pf (base : Base) (path : List Acc) (k : Kind) (m : MarkA) : PFact := ⟨base, path, k, m⟩
def cf (base : Base) (path : List Acc) (k : Kind) (m : MarkA) : AFact := ⟨⟨base, path, k, m⟩, false⟩

/-- `a = b.f` as the CURRENT `StatementSummaryBuilder.read` builds it (keepAllExcept). Kept only to show
    finding F2; the new builder is `loadF'`. -/
def loadF : Stmt :=
  { touched := [a, b]
    edges := [ (pf b [] (star (.set [f])) .star, pf b [] (star Excl.empty) .star),
               (pf b [f] (star Excl.empty) .star, pf b [f] (star Excl.empty) .star),
               (pf b [f] (star Excl.empty) .star, pf a [] (star Excl.empty) .star) ] }

/-- `a = b.f` with the identity keep edge `b.* -> b.*` (the new builder shape). -/
def loadF' : Stmt :=
  { touched := [a, b]
    edges := [ (pf b [] (star Excl.empty) .star, pf b [] (star Excl.empty) .star),
               (pf b [f] (star Excl.empty) .star, pf a [] (star Excl.empty) .star) ] }

/-- `a.f = b` (strong update), as `StatementSummaryBuilder.write` builds it. -/
def storeF : Stmt :=
  { touched := [a, b]
    edges := [ (pf a [] (star (.set [f])) .star, pf a [] (star Excl.empty) .star),
               (pf b [] (star Excl.empty) .star, pf b [] (star Excl.empty) .star),
               (pf b [] (star Excl.empty) .star, pf a [f] (star Excl.empty) .star) ] }

def onBase (base : Base) (r : Res) : List AFact := r.facts.filter (fun q => Nat.beq q.fact.base base)

/-! ### a = b.f -/

-- 1) (x,.f,*,E,*) -> (b,.f,*,E,*)  gives  (a,.,*,E,*)
example : onBase a (transfer allCounted 8 loadF' (cf b [f] (star E1) .star))
    = [cf a [] (star (E1.union (Excl.empty.union Excl.empty))) .star] := by decide
-- 2) (b,.,*,E,*)  gives  (a,.,[any],{},*)  in the demand layer
example : onBase a (transfer allCounted 8 loadF' (cf b [] (star E1) .star))
    = [⟨pf a [] .any .star, true⟩] := by decide
-- 3) (b,.,*,{f},*)  gives nothing for a
example : onBase a (transfer allCounted 8 loadF' (cf b [] (star (.set [f])) .star)) = [] := by decide
-- 4) (b,.,[any],{},*)  gives  (a,.,[any],{},*)
example : onBase a (transfer allCounted 8 loadF' (cf b [] .any .star))
    = [cf a [] .any .star] := by decide
-- 5) (b,.,$,{},*)  is dropped for a
example : onBase a (transfer allCounted 8 loadF' (cf b [] .exact .star)) = [] := by decide
-- no exclusion update and no request on a field read
example : (transfer allCounted 8 loadF' (cf b [] (star E1) .star)).reqs = [] := by decide

/-! ### a.f = b -/

-- 1) (b,.g,*,E,*) gives (a,.f.g,*,E,*) when the limit allows it ...
example : onBase a (transfer allCounted 2 storeF (cf b [g] (star E1) .star))
    = [cf a [f, g] (star E1) .star] := by decide
-- ... and (a,.f,[any],{},*) under the field limit 1 (a demand fact)
example : onBase a (transfer allCounted 1 storeF (cf b [g] (star E1) .star))
    = [⟨pf a [f] .any .star, true⟩] := by decide
-- 2) (a,.f,*,E,*) is dropped (strong update)
example : onBase a (transfer allCounted 8 storeF (cf a [f] (star E1) .star)) = [] := by decide
-- 3) (a,.,*,E,*) gives (a,.,*,E ∪ {f},*): exclusion update only
example : onBase a (transfer allCounted 8 storeF (cf a [] (star E1) .star))
    = [cf a [] (star (E1.union ((Excl.set [f]).union Excl.empty))) .star] := by decide
example : (transfer allCounted 8 storeF (cf a [] (star E1) .star)).reqs = [] := by decide

/-! ### sink(x) for mark T -/

def sinkX : PFact := pf x [] .exact (.conc T)
def initStar : PFact := pf x [] (star Excl.empty) .star

example : check initStar (cf x [] .exact (.conc T)) sinkX = .triggered := by decide
example : check initStar (cf x [f] .exact (.conc T)) sinkX = .none := by decide
example : check initStar (cf x [] .any (.conc T)) sinkX = .triggered := by decide
example : check initStar (cf x [] (star Excl.empty) .star) sinkX = .request T := by decide
-- an abstract fact below x does not reach x itself: no request
example : check initStar (cf x [f] (star Excl.empty) .star) sinkX = .none := by decide

/-! ### mark request answers (section 4 of the task) -/

def reqInit : PFact := pf x [f] (star Excl.empty) .star

-- exact match: emit (x,.f,$,{},T)
example : answerInit reqInit (pf x [f] .exact (.conc T)) T = pf x [f] .exact (.conc T) := by decide
-- deeper added fact (x,.f.g.h,$,{},T): emit (x,.f,*,{},T); it starts as (x,.f,[any],{},T)
-- in the DEMAND layer (the `~` premise). The chain is never deeper than the request.
example : answerInit reqInit (pf x [f, g, h] .exact (.conc T)) T = pf x [f] (star Excl.empty) (.conc T) := by decide
example : startFact (answerInit reqInit (pf x [f, g, h] .exact (.conc T)) T)
    = ⟨pf x [f] .any (.conc T), true⟩ := by decide
-- both added facts overlap the request
example : overlapB (pf x [f] .exact (.conc T)) reqInit = true := by decide
example : overlapB (pf x [f, g, h] .exact (.conc T)) reqInit = true := by decide

/-! ### summary application -/

-- callee summary (x,.f,*,{},*) -> (r,.,*,{},*); caller fact (x,.f.g,$,{},T)
def r0 : Base := 20
example : (applyEdge (cf x [f, g] .exact (.conc T)) (pf x [f] (star Excl.empty) .star)
      (pf r0 [] (star Excl.empty) .star)).facts
    = [cf r0 [g] .exact (.conc T)] := by decide
-- a premise with a concrete mark does not apply to a mark-abstract caller fact:
-- it raises a request instead
example : (applyEdge (cf x [f] (star Excl.empty) .star) (pf x [f] .exact (.conc T))
      (pf r0 [] .exact (.conc T))).reqs = [T] := by decide
-- the caller fact is more abstract than the premise: the correlation is lost
example : (applyEdge (cf x [] (star Excl.empty) .star) (pf x [f] (star Excl.empty) .star)
      (pf r0 [] (star Excl.empty) .star)).facts
    = [⟨pf r0 [] .any .star, true⟩] := by decide

/-! ### provenance: no [any] in the final fact does not mean exact -/

-- (b,.h,[any],T) is a demand fact; a rule that reads b.h exactly gives (r,.,$,T).
-- The result has no [any], but it is still a demand fact (approx stays true).
example : (applyEdge ⟨pf b [h] .any (.conc T), true⟩ (pf b [h] .exact .star)
      (pf r0 [] .exact .star)).facts
    = [⟨pf r0 [] .exact (.conc T), true⟩] := by decide


/-! ### the read builder must keep the read base with ONE identity edge -/

-- With the current builder shape (keepAllExcept split), a read of the abstract
-- fact b.* creates the spurious demand fact b.f.[any] on the read base itself:
example : onBase b (transfer allCounted 8 loadF (cf b [] (star E1) .star))
    = [cf b [] (star (E1.union ((Excl.set [f]).union Excl.empty))) .star,
       ⟨pf b [f] .any .star, true⟩] := by decide

-- The read base stays exact and complete:
example : onBase b (transfer allCounted 8 loadF' (cf b [] (star E1) .star))
    = [cf b [] (star (E1.union (Excl.empty.union Excl.empty))) .star] := by decide
-- and the result on a is the same as before:
example : onBase a (transfer allCounted 8 loadF' (cf b [] (star E1) .star))
    = [⟨pf a [] .any .star, true⟩] := by decide
example : onBase a (transfer allCounted 8 loadF' (cf b [f] (star E1) .star))
    = [cf a [] (star (E1.union (Excl.empty.union Excl.empty))) .star] := by decide

/-! ### a two-level strong update (static `C.s = v` with one ClassStatic base) -/

def S : Base := 30   -- the single ClassStatic base of the current code
def C : Acc := 40    -- ClassStaticAccessor(C)
def s' : Acc := 41   -- field s
def v : Base := 31

/-- `C.s = v` as the current builder emits it: keepAllExcept at depth 1 and 2. -/
def storeStatic : Stmt :=
  { touched := [S, v]
    edges := [ (pf S [] (star (.set [C])) .star, pf S [] (star Excl.empty) .star),
               (pf S [C] (star (.set [s'])) .star, pf S [C] (star Excl.empty) .star),
               (pf v [] (star Excl.empty) .star, pf v [] (star Excl.empty) .star),
               (pf v [] (star Excl.empty) .star, pf S [C, s'] (star Excl.empty) .star) ] }

-- The abstract static fact gets a demand fact <static>.C.[any] on EVERY static write:
example : onBase S (transfer allCounted 8 storeStatic (cf S [] (star Excl.empty) .star))
    = [cf S [] (star (Excl.empty.union ((Excl.set [C]).union Excl.empty))) .star,
       ⟨pf S [C] .any .star, true⟩] := by decide

/-- With one base per class (`StaticBase(C)`), the same write is one level deep. -/
def SC : Base := 32
def storeStatic' : Stmt :=
  { touched := [SC, v]
    edges := [ (pf SC [] (star (.set [s'])) .star, pf SC [] (star Excl.empty) .star),
               (pf v [] (star Excl.empty) .star, pf v [] (star Excl.empty) .star),
               (pf v [] (star Excl.empty) .star, pf SC [s'] (star Excl.empty) .star) ] }

example : onBase SC (transfer allCounted 8 storeStatic' (cf SC [] (star Excl.empty) .star))
    = [cf SC [] (star (Excl.empty.union ((Excl.set [s']).union Excl.empty))) .star] := by decide

/-! ### normal form (F9) -/

-- (a) a mark-producing exact rule on the abstract fact b.*: without the normal form the
-- result would be (a, ., */Universe, T). With it the result is (a, ., $, T), a demand fact.
example : (applyEdge (cf b [] (star E1) .star) (pf b [] .exact .star) (pf a [] .exact (.conc T))).facts
    = [⟨pf a [] .exact (.conc T), true⟩] := by decide
-- (b) a demand summary through an exact premise on (b, ., */Universe): the result is not a `*` leaf
example : (applySummary (cf b [] (star .univ) .star) (pf b [] .exact .star) ⟨pf a [] .exact .star, true⟩).facts
    = [⟨pf a [] .exact .star, true⟩] := by decide

/-! ### the abstraction choices satisfy the contract C1 -/

-- a fact is applicable to itself (also an [any] fact)
example : applicable (pf x [f] .any (.conc T)) (pf x [f] .any (.conc T)) = true := by decide
example : applicable (pf x [f] .exact (.conc T)) (pf x [f] .exact (.conc T)) = true := by decide
example : applicable (pf x [f] (star E1) .star) (pf x [f] (star E1) .star) = true := by decide
-- the * projection of an [any] added fact covers it
example : applicable (pf x [f] (star Excl.empty) .star) (pf x [f] .any (.conc T)) = true := by decide
-- the most abstract fact covers every fact on its base
example : applicable (pf x [] (star Excl.empty) .star) (pf x [f, g] .exact (.conc T)) = true := by decide
example : applicable (pf x [] (star Excl.empty) .star) (pf x [] .any .star) = true := by decide
-- the syntactic [any] rule: an [any] premise does not serve a concrete caller fact
example : applicable (pf x [f] .any (.conc T)) (pf x [f, g] .exact (.conc T)) = false := by decide
-- a premise with an exclusion does not serve the abstract fact without it
example : applicable (pf x [] (star (.set [f])) .star) (pf x [] (star Excl.empty) .star) = false := by decide

/-! ### F16: an uncorrelated result can still be complete -/

-- an any-field rule "every location under b flows somewhere under a": from the abstract fact
-- b.*/{} the result (a, ., [any], *) is EXACT (no exclusion restricts the correlation).
-- This is the model result. The implementation applies W6 (ap.md §2.3, F41) and puts every
-- [any] conclusion in the demand layer (`Invariant.demand_of_any_ok`).
example : (applyEdge (cf b [] (star Excl.empty) .star) (pf b [] (star Excl.empty) .star)
      (pf a [] .any .star)).facts = [cf a [] .any .star] := by decide
-- with an exclusion on the fact, the same result is a demand fact
example : (applyEdge (cf b [] (star E1) .star) (pf b [] (star Excl.empty) .star)
      (pf a [] .any .star)).facts = [⟨pf a [] .any .star, true⟩] := by decide

/-! ### F20: identity edges of rules and the self-write -/

def z : Base := zeroBase
/-- `x = source()` without the identity edge for the zero fact: the zero fact dies. -/
def srcBad : Stmt :=
  { touched := [z, x], edges := [ (pf z [] .exact (.conc zeroMark), pf x [] .exact (.conc T)) ] }
/-- with the identity edge `zero -> zero` -/
def srcOk : Stmt :=
  { touched := [z, x], edges := [ (pf z [] .exact (.conc zeroMark), pf z [] .exact (.conc zeroMark)),
                                  (pf z [] .exact (.conc zeroMark), pf x [] .exact (.conc T)) ] }
example : onBase z (transfer allCounted 8 srcBad ⟨zeroFact, false⟩) = [] := by decide
example : onBase z (transfer allCounted 8 srcOk ⟨zeroFact, false⟩) = [⟨zeroFact, false⟩] := by decide
example : onBase x (transfer allCounted 8 srcOk ⟨zeroFact, false⟩) = [cf x [] .exact (.conc T)] := by decide

/-- `a.f = a` (self-write) as the builder must emit it: no identity edge for `a`. -/
def selfW : Stmt :=
  { touched := [a], edges := [ (pf a [] (star (.set [f])) .star, pf a [] (star Excl.empty) .star),
                               (pf a [] (star Excl.empty) .star, pf a [f] (star Excl.empty) .star) ] }
/-- the same with the identity edge that the general write row has for the value base -/
def selfWBad : Stmt :=
  { touched := [a], edges := selfW.edges ++ [ (pf a [] (star Excl.empty) .star, pf a [] (star Excl.empty) .star) ] }
-- the old value a.f.g moves to a.f.f.g; a.f.g is killed
example : onBase a (transfer allCounted 8 selfW (cf a [f, g] .exact (.conc T)))
    = [cf a [f, f, g] .exact (.conc T)] := by decide
-- with the identity edge the killed a.f.g comes back as a COMPLETE fact (a false flow)
example : onBase a (transfer allCounted 8 selfWBad (cf a [f, g] .exact (.conc T)))
    = [cf a [f, f, g] .exact (.conc T), cf a [f, g] .exact (.conc T)] := by decide

/-! ### F1: an edge without `[any]` can still be a demand edge (conditional source) -/

-- Under the answer initial (x,.,*,{},T) the start fact is (x,.,[any],{},T) in the demand layer.
-- `a = x.f` keeps the [any] (read case 4) and the demand layer:
def ansI : PFact := answerInit (pf x [] (star Excl.empty) .star) (pf x [f, g] .exact (.conc T)) T
example : ansI = pf x [] (star Excl.empty) (.conc T) := by decide
example : onBase a (transfer allCounted 8 loadF' (startFact ⟨b, [], (star Excl.empty), (.conc T)⟩))
    = [⟨pf a [] .any (.conc T), true⟩] := by decide
-- `r = tag(a)`: conditional source "a carries T ⇒ r gets T2". Its condition matches the
-- [any] fact; the result (r,.,$,T2) has NO [any], but it stays in the demand layer.
def T2 : Mark := 6
def tagRule : Stmt :=
  { touched := [a, r0],
    edges := [ (pf a [] (star Excl.empty) .star, pf a [] (star Excl.empty) .star),
               (pf a [] .exact (.conc T), pf r0 [] .exact (.conc T2)) ] }
example : onBase r0 (transfer allCounted 8 tagRule ⟨pf a [] .any (.conc T), true⟩)
    = [⟨pf r0 [] .exact (.conc T2), true⟩] := by decide
-- the same without any request: a field-limit cut puts the zero edge into the demand layer
example : onBase a (transfer allCounted 1 storeF (cf b [g] .exact (.conc T)))
    = [⟨pf a [f] .any (.conc T), true⟩] := by decide
example : onBase r0 (transfer allCounted 8 tagRule ⟨pf a [] .any (.conc T), true⟩)
    = [⟨pf r0 [] .exact (.conc T2), true⟩] := by decide
-- classification: complete = normal layer and no [any] in the conclusion
example : (⟨pf r0 [] .exact (.conc T2), true⟩ : AFact).complete = false := by decide
example : (⟨pf a [] .any (.conc T), false⟩ : AFact).complete = false := by decide
example : (cf a [] (star E1) .star).complete = true := by decide

/-! ### the abstraction policy (spec §6.1, §6.2) satisfies the contract C1 -/

def dem : MethodId → List PFact := fun _ => [pf x [f] .any .star]
-- zero serves zero
example : policy dem 0 zeroFact = zeroFact := by decide
-- a demand covers the chain: the * projection with the mark *
example : policy dem 0 (pf x [f, g] .exact (.conc T)) = pf x [f, g] (star Excl.empty) .star := by decide
-- no demand: the most abstract fact
example : policy dem 0 (pf x [g] .exact (.conc T)) = pf x [] (star Excl.empty) .star := by decide
example : applicable (policy dem 0 (pf x [f, g] .exact (.conc T))) (pf x [f, g] .exact (.conc T)) = true := by decide
example : applicable (policy dem 0 (pf x [g] .any (.conc T))) (pf x [g] .any (.conc T)) = true := by decide

end ApSpec.Cases

/-! ## Round 5: cleaners with a mark exclusion, and type filters (spec §4.7, §4.8)

  The names of this section: the base `x = 1` (and two other bases `y = 4`, `r = 5`), the
  accessors `f = 2`, `g = 3`, the marks `T = 7`, `U = 8`, and the tail `st = *` with the empty
  exclusion. A mark `*∖{T}` is `.starEx [T]`. Each vector is checked by `decide`, except the
  vectors on `markGate`: `Gate` has no `DecidableEq`, so the kernel checks them by `rfl`. -/

namespace ApSpec.CleanCases
open ApSpec

def x : Base := 1
def y : Base := 4
def r : Base := 5
def f : Acc := 2
def g : Acc := 3
def T : Mark := 7
def U : Mark := 8
def st : Kind := .star (.set [])

/-- A final fact in the normal layer. -/
def cf (b : Base) (p : List Acc) (k : Kind) (m : MarkA) : AFact := ⟨⟨b, p, k, m⟩, false⟩
/-- A final fact in the demand layer. -/
def df (b : Base) (p : List Acc) (k : Kind) (m : MarkA) : AFact := ⟨⟨b, p, k, m⟩, true⟩

/-- The result of the cleaner as a pair (facts, requests). -/
def cr (cl : Cleaner) (c : AFact) : List AFact × List Mark :=
  ((cleanRes cl c).facts, (cleanRes cl c).reqs)

/-! ### The cleaner of `T` on `x.*` (everything strictly below `x`) -/

def clBelow : Cleaner := ⟨x, [], .below, some T⟩

-- a `*` fact at `x`: the location `x` itself is not cleaned, the locations below it are.
-- So the fact is partly cleaned: it continues as `*∖{T}`, and the request `T` goes to the premise.
example : cleanPos clBelow (cf x [] st .star).fact = .part := by decide
theorem clBelow_star_at : cr clBelow (cf x [] st .star) = ([cf x [] st (.starEx [T])], [T]) := by
  decide
#print axioms clBelow_star_at

-- a `*` fact at `x.f`: every location is cleaned. The fact continues as `*∖{T}`, no request.
example : cleanPos clBelow (cf x [f] st .star).fact = .inside := by decide
theorem clBelow_star_below : cr clBelow (cf x [f] st .star) = ([cf x [f] st (.starEx [T])], []) := by
  decide
#print axioms clBelow_star_below

-- a concrete `T` fact at `x.f`: dropped
theorem clBelow_conc_T : cr clBelow (cf x [f] .exact (.conc T)) = ([], []) := by decide
#print axioms clBelow_conc_T

-- `(x,.,[any],T)`: only the position `x` itself is not cleaned, so the fact keeps only `(x,.,$,T)`
example : cleanPos clBelow (df x [] .any (.conc T)).fact = .part := by decide
theorem clBelow_any_T : cr clBelow (df x [] .any (.conc T)) = ([df x [] .exact (.conc T)], []) := by
  decide
#print axioms clBelow_any_T

-- a concrete fact with another mark `U`: unchanged
theorem clBelow_conc_U : cr clBelow (cf x [f] .exact (.conc U)) = ([cf x [f] .exact (.conc U)], []) := by
  decide
#print axioms clBelow_conc_U

-- a fact on another base: unchanged
example : cleanPos clBelow (cf y [f] st .star).fact = .disjoint := by decide
theorem clBelow_other_base : cr clBelow (cf y [f] st .star) = ([cf y [f] st .star], []) := by decide
#print axioms clBelow_other_base
example : cr clBelow (cf y [f] .exact (.conc T)) = ([cf y [f] .exact (.conc T)], []) := by decide

-- a second cleaner adds its mark to the exclusion: `*∖{T}` becomes `*∖{U, T}`
example : cr ⟨x, [], .below, some U⟩ (cf x [f] st (.starEx [T])) =
    ([cf x [f] st (.starEx [U, T])], []) := by decide

/-! ### The cleaner of `T` on `x.f` only (`exact`) -/

def clExact : Cleaner := ⟨x, [f], .exact, some T⟩

-- a `*` fact at `x.f`: the location `x.f` itself is cleaned, the locations below it are not.
-- So the fact is partly cleaned: `*∖{T}`, and the request `T`.
example : cleanPos clExact (cf x [f] st .star).fact = .part := by decide
theorem clExact_star_at : cr clExact (cf x [f] st .star) = ([cf x [f] st (.starEx [T])], [T]) := by
  decide
#print axioms clExact_star_at

-- `(x,.f,$,T)`: dropped
example : cleanPos clExact (cf x [f] .exact (.conc T)).fact = .inside := by decide
theorem clExact_conc_at : cr clExact (cf x [f] .exact (.conc T)) = ([], []) := by decide
#print axioms clExact_conc_at

-- `(x,.f.g,$,T)`: below the cleaned location, unchanged
example : cleanPos clExact (cf x [f, g] .exact (.conc T)).fact = .disjoint := by decide
theorem clExact_conc_below : cr clExact (cf x [f, g] .exact (.conc T)) =
    ([cf x [f, g] .exact (.conc T)], []) := by decide
#print axioms clExact_conc_below

/-! ### The cleaner of every mark on `x` and everything below it -/

def clAll : Cleaner := ⟨x, [], .atAndBelow, none⟩

-- a `*` fact at `x.f`: every location is cleaned, for every mark: dropped
theorem clAll_star_below : cr clAll (cf x [f] st .star) = ([], []) := by decide
#print axioms clAll_star_below

-- a `*` fact on another base: unchanged
theorem clAll_other_base : cr clAll (cf y [f] st .star) = ([cf y [f] st .star], []) := by decide
#print axioms clAll_other_base

/-! ### The result mark `markComp`, and a summary conclusion behind a cleaner -/

-- a target `*∖{T}` stops the concrete mark `T` and lets `U` through
theorem markComp_stops : markComp (.starEx [T]) (.conc T) = none := by decide
theorem markComp_passes : markComp (.starEx [T]) (.conc U) = some (.conc U) := by decide
theorem markComp_star : markComp (.starEx [T]) .star = some (.starEx [T]) := by decide
#print axioms markComp_stops
#print axioms markComp_passes
#print axioms markComp_star
-- two exclusions join
example : markComp (.starEx [T]) (.starEx [U]) = some (.starEx [T, U]) := by decide

/-- The callee summary premise `(x,.,*,{},*)` and its conclusion `(r,.,*,{},*∖{T})`: a cleaner of
    `T` is on the path from the entry to the exit. -/
def sumI : PFact := ⟨x, [], st, .star⟩
def sumC : PFact := ⟨r, [], st, .starEx [T]⟩

-- a caller fact with the mark `T`: no fact
theorem applyEdge_cleaned_T : (applyEdge (cf x [f] .exact (.conc T)) sumI sumC).facts = [] := by decide
-- a caller fact with the mark `U`: the fact `(r,.f,$,U)`
theorem applyEdge_cleaned_U :
    (applyEdge (cf x [f] .exact (.conc U)) sumI sumC).facts = [cf r [f] .exact (.conc U)] := by decide
#print axioms applyEdge_cleaned_T
#print axioms applyEdge_cleaned_U
-- no request in both
example : (applyEdge (cf x [f] .exact (.conc T)) sumI sumC).reqs = [] := by decide
example : (applyEdge (cf x [f] .exact (.conc U)) sumI sumC).reqs = [] := by decide
-- a `*` caller fact: the result keeps the exclusion, `(r,.f,*,{},*∖{T})` in the normal layer
example : (applyEdge (cf x [f] st .star) sumI sumC).facts = [cf r [f] st (.starEx [T])] := by decide
-- the same through `applySummary` (the summary edge is in the normal layer)
example : (applySummary (cf x [f] .exact (.conc T)) sumI ⟨sumC, false⟩).facts = [] := by decide
example : (applySummary (cf x [f] .exact (.conc U)) sumI ⟨sumC, false⟩).facts =
    [cf r [f] .exact (.conc U)] := by decide

/-! ### The sink check on a `*∖{T}` fact -/

def sinkT : PFact := ⟨x, [], .exact, .conc T⟩
def sinkU : PFact := ⟨x, [], .exact, .conc U⟩

-- under a `*` premise: a sink for the cleaned mark `T` gives nothing (no request); a sink for `U`
-- requests `U`
theorem check_cleaned_T : check sumI (cf x [] st (.starEx [T])) sinkT = .none := by decide
theorem check_cleaned_U : check sumI (cf x [] st (.starEx [T])) sinkU = .request U := by decide
#print axioms check_cleaned_T
#print axioms check_cleaned_U
-- under a concrete premise `T`: the cleaned mark does not trigger
example : check ⟨x, [], st, .conc T⟩ (cf x [] st (.starEx [T])) sinkT = .none := by decide

/-! ### The mark gate and the climb of a request -/

-- a summary premise with the mark `T` against a `*∖{T}` caller fact: no application, no request
theorem markGate_cleaned : markGate (.conc T) (.starEx [T]) = .no := rfl
-- against a `*∖{T}` caller fact, the premise mark `U` raises the request `U`
example : markGate (.conc U) (.starEx [T]) = .req U := rfl
#print axioms markGate_cleaned

-- the request `T` does not climb through an added fact `*∖{T}`; the request `U` does
theorem climbs_cleaned_T : climbsB (.starEx [T]) T = false := by decide
theorem climbs_cleaned_U : climbsB (.starEx [T]) U = true := by decide
#print axioms climbs_cleaned_T
#print axioms climbs_cleaned_U

/-! ### The type filter (spec §4.8) -/

/-- The type filter of `x`: the type of `x` has the field `f` but not the field `g`. As the real
    checker does, the predicate reads only the first accessor of the path. -/
def mayX : List Acc → Bool
  | []     => true
  | a :: _ => !Nat.beq a g

/-- The filter predicate is prefix-closed (the field `filtPrefix` of `Program.WF`). -/
theorem mayX_prefix : ∀ p q, mayX (p ++ q) = true → mayX p = true
  | [],     _, _ => rfl
  | _ :: _, _, h => h
#print axioms mayX_prefix

/-- The condition of rule `filt` as a Boolean: the fact is on another base, or its path may exist. -/
def filtPassB (b : Base) (may : List Acc → Bool) (c : AFact) : Bool :=
  !Nat.beq c.fact.base b || may c.fact.path

/-- The Boolean is the condition of rule `filt` (and of `Flow.filt` for a location). -/
theorem filtPassB_iff (b : Base) (may : List Acc → Bool) (c : AFact) :
    filtPassB b may c = true ↔ (c.fact.base = b → may c.fact.path = true) := by
  unfold filtPassB
  cases hb : Nat.beq c.fact.base b with
  | false =>
    constructor
    · intro _ h
      rw [h, Nat.beq_refl] at hb
      cases hb
    · intro _
      rfl
  | true =>
    constructor
    · intro h _
      exact h
    · intro h
      exact h (Nat.eq_of_beq_eq_true hb)
#print axioms filtPassB_iff

-- on the base `x`, a fact passes the filter iff its path is accepted
theorem filt_star_root : filtPassB x mayX (cf x [] st .star) = true := by decide
theorem filt_field_f : filtPassB x mayX (cf x [f] st .star) = true := by decide
theorem filt_field_g : filtPassB x mayX (cf x [g] .exact (.conc T)) = false := by decide
#print axioms filt_star_root
#print axioms filt_field_f
#print axioms filt_field_g
example : filtPassB x mayX (cf x [f, g] .exact (.conc T)) = true := by decide
example : filtPassB x mayX (df x [g, f] .any (.conc T)) = false := by decide
-- the same as `mayX` on the path, for every fact on `x` in this list
example : ∀ c ∈ [cf x [] st .star, cf x [f] st .star, cf x [g] .exact (.conc T),
    cf x [f, g] .exact (.conc T), df x [g, f] .any (.conc T)],
    filtPassB x mayX c = mayX c.fact.path := by decide
-- another base: the filter of `x` does not apply
example : filtPassB x mayX (cf y [g] .exact (.conc T)) = true := by decide
-- a covering fact passes: the location `x.f.g` may exist, the fact `(x,.f,*)` covers it
example : mayX [f, g] = true ∧ filtPassB x mayX (cf x [f] st .star) = true := by decide

/-- A program with one type filter edge on `x`. It is well formed: `mayX` is prefix-closed. -/
def Pfilt : Program := ⟨fun _ => 0, fun _ => 1, [(0, 0, .filt x mayX, 1)]⟩

theorem Pfilt_wf : Pfilt.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M n s n' hE
    cases hE with
    | tail _ hE => cases hE
  · intro M n c n' hE
    cases hE with
    | tail _ hE => cases hE
  · intro M n c n' hE
    cases hE with
    | tail _ hE => cases hE
  · intro M n b may n' hE
    cases hE with
    | head => exact mayX_prefix
    | tail _ hE => cases hE
#print axioms Pfilt_wf

end ApSpec.CleanCases
