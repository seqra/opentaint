import HeadSafety
namespace HeadAlternating
open NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000
local instance : BEq Row where beq a b := decide (a = b)
local instance : LawfulBEq Row where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
abbrev Edge := Ap × Value
abbrev Saved := UniformAlternating.Saved
abbrev Data := UniformAlternating.Data
abbrev State := UniformAlternating.State
def colors : List Color := [.t,.u]
def normalGuidance (a : Ap) : Ap := if a.tail == .must then {a with tail := .may} else a

def reverseSaved (e : Edge) : Edge :=
  let mustInput := e.1.tail == .must
  ( {e.2.ap with tail := if e.2.ap.tail == .must then .star else e.2.ap.tail},
    { ap := {e.1 with tail := if mustInput then .may else e.1.tail,e := []}
      demand := mustInput
      h := false })

def views (back : Bool) (all : List Saved) : List Edge :=
  all.map fun s => if s.back == back then s.edge else reverseSaved s.edge

/-- Source relations generate a literal mark/path. They do not copy any
    input suffix. MUST guards use the retained definite native lane. -/
def read (e : Edge) (a : Offered) : Option Value := do
  if e.1.base != a.ap.base || e.1.mark != a.ap.mark then none else
  let known := a.ap.tail == .must && DefiniteMustReplay.covers a.ap e.1
  let overlap := match dropHead e.1.path a.ap.path with
    | some [] => e.1.tail != .must || known
    | some (_ :: _) => e.1.tail != .exact && e.1.tail != .must
    | none => match dropHead a.ap.path e.1.path with
      | some (f :: _) => a.ap.tail != .exact && !a.ap.e.contains f
      | _ => false
  let allowed := if e.1.tail == .must then known else overlap
  if !allowed then none else
  some { e.2 with
    ap := {e.2.ap with base := p}
    demand := e.2.demand || a.demand ||
      (a.ap.tail != .must && e.1.path != a.ap.path &&
        (dropHead a.ap.path e.1.path).isSome) }

def firstFields (back : Bool) (row : Row) (rows : List Row) (saved : List Saved) : List Nat :=
  let heads := (rows.filter fun r => decide (r.exit = row.exit)).map (·.entry) ++
    (views back saved).map (·.1)
  (heads.filterMap fun h =>
    if h.base != row.entry.base || h.mark != row.entry.mark then none else
    match dropHead row.entry.path h.path with
    | some (f :: _) => some f
    | _ => none).eraseDups

def prepare (run k : Nat) (back : Bool) (row : Row) (rows : List Row)
    (saved : List Saved) (actual : Offered) : List Seed :=
  let base := HeadPolicy.emit run k back row.entry actual
  let children := if (row.entry.tail == .may || row.entry.tail == .ne) && !base.isEmpty then
    (firstFields back row rows saved).flatMap fun f =>
      let head := {row.entry with path := row.entry.path ++ [f],tail := .may}
      (HeadPolicy.emit run k back head actual).filter fun q =>
        q.ap.path == head.path && decide (q.ap.path.length ≤ row.entry.path.length+1)
  else []
  (base ++ children).eraseDups

def candidates (run k : Nat) (back : Bool) (rows : List Row) (saved : List Saved)
    (domains : List Offered) : List Edge :=
  (domains.flatMap fun a =>
    let cases := if run == 1 then colors.flatMap fun m =>
      if a.ap.mark == some m.id then
        (generate m (star p [] m)).map fun c => ((star p [] m).ap,cut k c)
      else []
    else rows.flatMap fun row =>
      let qs := prepare run k back row rows saved a
      qs.flatMap fun q => colors.flatMap fun m =>
        let cs := if back then reverseGenerate k m q else generate m q
        cs.filterMap fun c => DifferentUniformReply.publish run k back row qs q (cut k c)
    cases).eraseDups

def asInput (back : Bool) (v : Value) : Offered :=
  ⟨{v.ap with base := if back then ret else p},v.demand⟩
def actualReplies (enabled : Bool) (run k : Nat) (rows : List Row) (saved : List Saved)
    (current : List Edge) (actual : Offered) : List Value :=
  let back := run % 2 == 0
  let ps := rows.flatMap fun row => prepare run k back row rows saved actual
  let raw := (views back saved).filterMap (fun e => read e actual) ++
    (canonicalEdges current).filterMap fun e =>
      if run == 1 || ps.any (fun q => decide (q.ap = e.1)) then read e actual else none
  UniformActual.foldValues (!enabled || back) [] (packet raw)

def normalizeContinuation (enabled : Bool) (back : Bool) (vs : List Value) : List Value :=
  UniformActual.foldValues (!enabled || back) [] (packet vs)

def emptyData : Data := ⟨[],[],List.replicate 4 []⟩
def initialData (back : Bool) : Data :=
  ⟨[],[],[if back then [rootMay .u] else [⟨source.ap,source.demand,false⟩]] ++ List.replicate 3 []⟩

def round (enabled : Bool) (run k : Nat) (rows : List Row) (saved : List Saved) (d : Data) : Data := Id.run do
  let back := run % 2 == 0
  let mut state := d
  for j in List.range 3 do
    let mut out := state.offers[j+1]!
    for v in state.offers[j]! do
      let a := asInput back v
      state := {state with domains := (state.domains ++ [a]).eraseDups}
      out := out ++ actualReplies enabled run k rows saved state.raw a
    state := {state with offers := state.offers.set (j+1) (normalizeContinuation enabled back out)}
  let fresh := candidates run k back rows saved state.domains
  return {state with raw := (state.raw ++ fresh).eraseDups}

def analyze (enabled : Bool) (fuel run k : Nat) (rows : List Row) (saved : List Saved) : Data :=
  fuel.rec (initialData (run % 2 == 0)) (fun _ d => round enabled run k rows saved d)

def outputRows (d : Data) : List Row :=
  (d.raw.filterMap fun e => if e.2.demand then some ⟨normalGuidance e.2.ap,normalGuidance e.1⟩ else none).eraseDups

def outputSaved (back : Bool) (old : List Saved) (d : Data) : List Saved :=
  (old ++ (canonicalEdges d.raw).filterMap (fun (e : Edge) => if e.2.demand then none
    else some (⟨if back then reverseSaved e else e,back⟩ : Saved))).eraseDups

def initial : State := ⟨[],[],true,false,false,emptyData⟩
def quiet (report : Bool) (saved : List Saved) : State := ⟨[],saved,false,false,report,emptyData⟩
def limit (run : Nat) : Nat := max 1 (run-1)

def producerHit (d : Data) : Bool := d.offers.getLast!.any fun v =>
  v.ap.mark == source.ap.mark &&
    ((match dropHead v.ap.path source.ap.path with
      | some rest => admits v.ap.tail v.ap.e rest
      | none => false) ||
      (source.ap.tail == .must && (dropHead source.ap.path v.ap.path).isSome))

def dataStep (enabled : Bool) (run : Nat) (old : State) : State :=
  let back := run % 2 == 0
  let active := if back then old.observationActive else old.sourceAllowed
  if !active then quiet old.report old.saved else
  let data := analyze enabled 12 run (limit run) old.rows old.saved
  let rows := outputRows data
  let saved := outputSaved back old.saved data
  if back then ⟨rows,saved,producerHit data,false,old.report,data⟩ else
    ⟨rows,saved,old.sourceAllowed,data.offers.getLast!.any (·.demand),
      old.report || data.offers.getLast!.any (fun v => !v.demand),data⟩
def forwardTarget (enabled : Bool) (run : Nat) (old : State) : Bool :=
  UniformSticky.seenDemand (fun data => data.offers.getLast!.any (·.demand))
    (round enabled run (limit run) old.rows old.saved) 12 (initialData false)

def step (enabled : Bool) (run : Nat) (old : State) : State :=
  let next := dataStep enabled run old
  if run % 2 == 1 && old.sourceAllowed then
    {next with observationActive := forwardTarget enabled run old} else next

def history (enabled : Bool) : Nat → State
  | 0 => initial
  | n+1 => step enabled (n+1) (history enabled n)

def stopped (run : Nat) (s : State) : Bool := run % 2 == 1 && s.rows.isEmpty && !s.observationActive


theorem quiet_never_restarts (enabled : Bool) (run : Nat) (report : Bool) (saved : List Saved) :
    step enabled run (quiet report saved) = quiet report saved := by simp [step,dataStep,quiet]
end HeadAlternating
