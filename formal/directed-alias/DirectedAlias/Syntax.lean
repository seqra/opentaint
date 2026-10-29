import DirectedAlias.ListSet

/-!
# Syntax of the structured IR

Statements and programs of the model (brief §3).
A program frame gives the entry roots of the variables.
-/

namespace DirectedAlias

/-- A local variable. -/
abbrev Var := Nat
/-- A field name. -/
abbrev Field := Nat
/-- A statement site (an allocation, unknown expression or call statement). -/
abbrev Site := Nat
/-- An entry root (this, an argument, or a static). Distinct roots are distinct objects (A1). -/
abbrev Root := Nat

/-- A concrete heap cell: a field, or an array element with its index. -/
inductive Cell where
  | fld (f : Field)
  | elem (i : Nat)
  deriving DecidableEq, Repr

/-- An abstract heap cell: a field, or any array element. -/
inductive ACell where
  | fld (f : Field)
  | elem
  deriving DecidableEq, Repr

/-- The abstraction of a concrete cell. It removes the array index. -/
def Cell.abs : Cell → ACell
  | .fld f => .fld f
  | .elem _ => .elem

/-- A statement. -/
inductive Stmt where
  /-- `x := new` at site `s`. -/
  | new (x : Var) (s : Site)
  /-- `x := null` (also constants: no origin). -/
  | null (x : Var)
  /-- `x := y`. -/
  | copy (x y : Var)
  /-- `x := y.f`. -/
  | load (x y : Var) (f : Field)
  /-- `x.f := y`. -/
  | store (x : Var) (f : Field) (y : Var)
  /-- `x := y[i]` for some index `i`. -/
  | aload (x y : Var)
  /-- `x[i] := y` for some index `i`. -/
  | astore (x y : Var)
  /-- `x := e` for an unknown expression `e` at site `s`. The result is a fresh object. -/
  | unknown (x : Var) (s : Site)
  /-- `ret := m(args)` for an unresolved call at site `s` (A2). -/
  | call (ret : Option Var) (s : Site) (args : List Var)
  deriving DecidableEq, Repr

/-- A structured program. -/
inductive Prog where
  | skip
  | stmt (st : Stmt)
  | seq (p q : Prog)
  /-- Nondeterministic choice: run `p` or run `q`. -/
  | choice (p q : Prog)
  /-- Run the body zero or more times. -/
  | loop (p : Prog)
  deriving DecidableEq, Repr

/-- The entry bindings: variable `x` holds root `r` at entry. Other variables hold null. -/
structure Frame where
  binds : List (Var × Root)
  deriving DecidableEq, Repr

/-- The root that variable `x` holds at entry, if any. The first binding wins. -/
def Frame.root? (fr : Frame) (x : Var) : Option Root :=
  fr.binds.lookup x

/-- The variables that the frame binds. -/
def Frame.vars (fr : Frame) : List Var :=
  fr.binds.map Prod.fst

/-- The roots that the frame uses. -/
def Frame.roots (fr : Frame) : List Root :=
  fr.binds.map Prod.snd

/-! ## Statement helpers -/

/-- The variables that a statement mentions. -/
def Stmt.vars : Stmt → List Var
  | .new x _ => [x]
  | .null x => [x]
  | .copy x y => [x, y]
  | .load x y _ => [x, y]
  | .store x _ y => [x, y]
  | .aload x y => [x, y]
  | .astore x y => [x, y]
  | .unknown x _ => [x]
  | .call ret _ args => ret.toList ++ args

/-- The fields that a statement mentions. -/
def Stmt.fields : Stmt → List Field
  | .load _ _ f => [f]
  | .store _ f _ => [f]
  | _ => []

/-- The site of a statement, if it has one. -/
def Stmt.site? : Stmt → Option Site
  | .new _ s => some s
  | .unknown _ s => some s
  | .call _ s _ => some s
  | _ => none

/-- The allocation site of a statement, if it is `new`. -/
def Stmt.newSite? : Stmt → Option Site
  | .new _ s => some s
  | _ => none

/-- The site of a statement that makes a fresh symbolic object (`unknown` or `call`). -/
def Stmt.freshSite? : Stmt → Option Site
  | .unknown _ s => some s
  | .call _ s _ => some s
  | _ => none

/-- The site of a statement, if it is `call`. -/
def Stmt.callSite? : Stmt → Option Site
  | .call _ s _ => some s
  | _ => none

/-! ## Program helpers -/

/-- The statements of a program, in syntax order, with repetitions. -/
def Prog.stmts : Prog → List Stmt
  | .skip => []
  | .stmt st => [st]
  | .seq p q => p.stmts ++ q.stmts
  | .choice p q => p.stmts ++ q.stmts
  | .loop p => p.stmts

/-- The statements of a program that are under a loop. -/
def Prog.loopStmts : Prog → List Stmt
  | .skip => []
  | .stmt _ => []
  | .seq p q => p.loopStmts ++ q.loopStmts
  | .choice p q => p.loopStmts ++ q.loopStmts
  | .loop p => p.stmts

/-- The variables that a program mentions. -/
def Prog.vars (p : Prog) : List Var :=
  p.stmts.flatMap Stmt.vars

/-- The fields that a program mentions. -/
def Prog.fields (p : Prog) : List Field :=
  p.stmts.flatMap Stmt.fields

/-- All site occurrences of a program, with repetitions. -/
def Prog.sites (p : Prog) : List Site :=
  p.stmts.filterMap Stmt.site?

/-- The site occurrences that are under a loop. -/
def Prog.loopSites (p : Prog) : List Site :=
  p.loopStmts.filterMap Stmt.site?

/-- The allocation sites of a program. -/
def Prog.newSites (p : Prog) : List Site :=
  p.stmts.filterMap Stmt.newSite?

/-- The sites of a program that make fresh symbolic objects. -/
def Prog.freshSites (p : Prog) : List Site :=
  p.stmts.filterMap Stmt.freshSite?

/-- The call sites of a program. -/
def Prog.callSites (p : Prog) : List Site :=
  p.stmts.filterMap Stmt.callSite?

/-- Site `s` runs at most one time in each execution of `p`:
it occurs at most one time in the syntax, and not under a loop. -/
def Prog.onceB (p : Prog) (s : Site) : Bool :=
  decide (p.sites.count s ≤ 1) && !(p.loopSites.contains s)

/-- The predicate form of `onceB`. -/
def Prog.once (p : Prog) (s : Site) : Prop :=
  p.onceB s = true

instance (p : Prog) (s : Site) : Decidable (p.once s) :=
  inferInstanceAs (Decidable (p.onceB s = true))

/-- A site under a loop is not `once`. -/
theorem Prog.not_once_of_loop {p : Prog} {s : Site} (h : s ∈ p.loopSites) : ¬ p.once s := by
  simp [Prog.once, Prog.onceB, h]

end DirectedAlias
