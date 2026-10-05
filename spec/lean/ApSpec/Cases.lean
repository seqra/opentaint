/-
  ApSpec.Cases — the cases of bidirectional-task.md as executable test vectors.

  Each `example` is checked by `decide` (kernel evaluation, no extra axiom).
  The same vectors are the reference for the Kotlin unit tests (spec §10).
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

/-! ### the abstraction choices satisfy (A1) -/

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
-- b.*/{} the result (a, ., [any], *) is EXACT (no exclusion restricts the correlation)
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

/-! ### the abstraction policy (spec §7.2) satisfies (A1) -/

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
