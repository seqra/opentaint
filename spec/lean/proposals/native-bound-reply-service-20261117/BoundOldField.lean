import BoundCore
import FlagOldField

namespace BoundOldField
open NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000
set_option linter.unusedSimpArgs false
local instance : BEq Row where beq a b := decide (a = b)
local instance : LawfulBEq Row where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

abbrev Edge := Ap × Value
structure Saved where
  edge : Edge
  back : Bool
  deriving DecidableEq, BEq, Repr
structure Data where
  domains : List Offered
  raw : List Edge
  complete : List Ap
  services : List (Ap × Nat)
  offers : List (List Value)
  closed : List Ap
  deriving DecidableEq, BEq, Repr
structure State where
  rows : List Row
  saved : List Saved
  complete : List Ap
  services : List (Ap × Nat)
  sourceAllowed : Bool
  observationActive : Bool
  report : Bool
  data : Data
  deriving DecidableEq, Repr

def colors : List Color := [.t,.u]
def h : Nat := 3

-- Two positive unary source actions assign the triggering T to a fresh result.
-- Both outputs are protected; protection does not change their layers.
-- This is a program change, not a change to the selected completion checks.
def gen (m : Color) (q : Seed) : List Value := ReplyBody.gen m q

def originalSource : Value := value p [f,g] .exact .t false
-- Ordinary entry assignment at an exact point; no field replacement.
def entryValues (_run k : Nat) : List Value :=
  [cut k originalSource]

def overlaps (q : Seed) (path : Path) : Bool :=
  (dropHead path q.ap.path).isSome ||
    ((dropHead q.ap.path path).isSome && q.ap.tail != .exact)

def reverseGen (k : Nat) (m : Color) (q : Seed) : List Value := ReplyBody.reverseGen k m q

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
        (gen m (star p [] m)).map fun c => ((star p [] m).ap,cut k c)
      else []
    else rows.flatMap fun row =>
      let qs := prepare run k back row rows saved a
      qs.flatMap fun q => colors.flatMap fun m =>
        let cs := if back then reverseGen k m q else gen m q
        cs.filterMap fun c => DifferentUniformReply.publish run k back row qs q (cut k c)
    cases).eraseDups

-- No new query is generated: only raw point queries already prepared by C2.
def queries (run k : Nat) (back : Bool) (rows : List Row) (saved : List Saved)
    (domains : List Offered) : List Seed :=
  (domains.flatMap fun a => rows.flatMap fun row => prepare run k back row rows saved a).eraseDups

/-- This leaf-model certificate explicitly checks every unbounded raw return.
    Generic closure and compositional justification live in CompleteClosure. -/
def completePoint (current : List Edge) (q : Seed) : Bool :=
  q.ap.tail == .exact && !q.demand && q.ap.mark.isSome &&
    q.ap.e.isEmpty && q.ap.mx.isEmpty &&
    (colors.flatMap fun m => gen m q).all (fun c =>
      !c.demand && !c.h && current.any (fun e => decide (e.1=q.ap ∧ e.2=c)))

def certify (run k : Nat) (rows : List Row) (saved : List Saved)
    (domains : List Offered) (current : List Edge) : List Ap :=
  if run < 3 || run % 2 == 0 then [] else
    ((queries run k false rows saved domains).filter (completePoint current)).map Seed.ap

def certifyMarks (run k : Nat) (rows : List Row) (saved : List Saved)
    (domains : List Offered) (current : List Edge) : List (Ap × Nat) :=
  if run < 3 || run % 2 == 0 then [] else
    (queries run k false rows saved domains).flatMap fun q =>
      (ScopedCore.extra current q (colors.flatMap fun m => gen m q)).map (fun mark => (q.ap,mark))


-- Current-owner completion only. Query execution checks all raw NORMAL states,
-- including boundary results rejected by C5. No new query is constructed.
def bodyClosed (k : Nat) (q : Seed) : Bool :=
  BoundCore.eligible q && (colors.flatMap fun m => gen m q).all
    (fun c => LayerCore.normalLayer c && decide (c.ap.path.length≤k))

def certifyClosed (run k : Nat) (rows : List Row) (saved : List Saved)
    (domains : List Offered) : List Ap :=
  if run < 3 || run % 2 == 0 then [] else
    ((queries run k false rows saved domains).filter (bodyClosed k)).map Seed.ap

def suppress (run : Nat) (complete : List Ap) (a : Offered) (e : Edge) : Bool :=
  run >= 3 && run % 2 == 1 && a.ap.tail == .exact && !a.demand &&
    a.ap.mark.isSome && a.ap.e.isEmpty && a.ap.mx.isEmpty &&
    complete.any (fun q => decide (q=a.ap)) &&
    e.1.tail == .star && e.2.demand && !e.2.h && e.2.ap.base == ret &&
    match dropHead e.1.path a.ap.path with
    | some (_ :: _) => true
    | _ => false

def suppressMark (run : Nat) (services : List (Ap × Nat)) (a : Offered) (e : Edge) : Bool :=
  match e.2.ap.mark with
  | none => false
  | some mark => suppress run
      (services.filterMap fun (q,m) => if m==mark then some q else none) a e

-- This is an on-demand proof for this scalar post-C5 reply. No per-region
-- flag or negative result is retained. All native service must apply here.
def suppressReply (run : Nat) (closed : List Ap) (service : List Edge)
    (native : List Value) (actual : Offered) (e : Edge) : Bool :=
  let q : Seed := ⟨actual.ap,false⟩
  let raw := colors.flatMap fun m => gen m q
  suppress run closed actual e && e.2.ap.mark.isSome &&
    LayerCore.completeFor service q raw e.2.ap &&
    ReplyCore.received native raw e.2.ap

-- Additional delivery restriction within each literal flag membership. The original
-- must be plain; its existing packet H is passed without changing query keys.
def suppressFlaggedReply (run : Nat) (closed : List Ap) (service : List Edge)
    (native : List Value) (actual : Offered) (originalH : Bool) (e : Edge) : Bool :=
  let q : Seed := ⟨actual.ap,false⟩
  let raw := colors.flatMap fun m => gen m q
  !originalH &&
    suppress run closed actual (e.1,{e.2 with h:=false}) &&
    FlagCore.completeFor service q raw e.2.ap e.2.h &&
    FlagCore.received native raw e.2.ap e.2.h

-- This view is the existing native transport for scalar packets. The
-- selected root has ZERO original, so there are no cycle-restored marks.
def readBound (e : Edge) (actual : Offered) (inputH : Bool) : Option Value :=
  (read e actual).map (fun c => {c with h:=c.h || inputH})

def suppressNativeReply (run : Nat) (closed : List Ap) (native : List Value)
    (actual : Offered) (inputH : Bool) (e : Edge) : Bool :=
  let q : Seed := ⟨actual.ap,false⟩
  let ctx : BoundCore.Context := ⟨inputH,[]⟩
  run >= 3 && run % 2 == 1 && BoundCore.eligible ⟨actual.ap,actual.demand⟩ &&
    closed.any (fun key => decide (key=actual.ap)) &&
    e.2.demand && e.2.ap.mark.isSome && e.2.ap.base==ret &&
    BoundCore.completeFor native q (colors.flatMap fun m => gen m q)
      e.2.ap ctx (BoundCore.flag ctx e.2)

-- The caller executes t=make(arg); result=t.h. The reverse read precedes
-- the reversed call. Only ordinary field transfer is added to the host.
def consumeH (v : Value) : Option Value :=
  match dropHead [h] v.ap.path with
  | some rest => some {v with ap := {v.ap with path := rest}}
  | none =>
    if v.ap.path.isEmpty && v.ap.tail != .exact && !v.ap.e.contains h then
      let tail : Tail := if v.ap.tail == .must then .must else .may
      let ap := {v.ap with path := [], tail := tail, e := []}
      some {v with ap := ap, demand := v.demand || (v.ap.tail != .must)}
    else none

def asInput (back : Bool) (k : Nat) (v : Value) : Offered :=
  let value := if back then cut k {v with ap := {v.ap with path := [h] ++ v.ap.path}} else v
  ⟨{value.ap with base := if back then ret else p},value.demand⟩

/-- A certificate is usable only after ALL its NORMAL return service has
    actually passed native application in this same reply packet. The leaf
    reference enumerates its support. An implementation can use service-row
    handles and an ephemeral delivery count, without reevaluating gen. -/
def delivered (raw : List Value) (q : Ap) : Bool :=
  (colors.flatMap fun m => gen m ⟨q,false⟩).all fun c =>
    !c.demand && !c.h && raw.any (fun n => decide (n={c with ap := {c.ap with base := p}}))

def deliveredMark (raw : List Value) (service : Ap × Nat) : Bool :=
  (ScopedCore.focus (colors.flatMap fun m => gen m ⟨service.1,false⟩) service.2).all fun c =>
    !c.demand && !c.h && raw.any (fun n => decide (n={c with ap := {c.ap with base := p}}))

def actualReplies (enabled : Bool) (run k : Nat) (rows : List Row) (saved : List Saved)
    (complete : List Ap) (services : List (Ap × Nat)) (closed : List Ap) (current : List Edge) (actual : Offered) (originalH : Bool := false) : List Value :=
  let back := run % 2 == 0
  let ps := rows.flatMap fun row => prepare run k back row rows saved actual
  let admitted := (canonicalEdges current).filter fun e =>
    run == 1 || ps.any (fun q => decide (q.ap=e.1))
  let savedReplies := (views back saved).filterMap (fun e => readBound e actual originalH)
  let native := savedReplies ++ admitted.filterMap (fun e => readBound e actual originalH)
  let ready := complete.filter (delivered native)
  let marksReady := services.filter (deliveredMark native)
  let raw := savedReplies ++ admitted.filterMap fun e =>
    if !(suppress run ready actual e || suppressMark run marksReady actual e ||
        suppressReply run closed (admitted ++ views back saved) native actual e ||
        suppressFlaggedReply run closed (admitted ++ views back saved) native actual originalH e ||
        suppressNativeReply run closed native actual originalH e) then readBound e actual originalH else none
  UniformActual.foldValues (!enabled || back) [] (packet raw)

def normalizeContinuation (enabled : Bool) (back : Bool) (vs : List Value) : List Value :=
  UniformActual.foldValues (!enabled || back) [] (packet vs)

def emptyData : Data := ⟨[],[],[],[],List.replicate 4 [],[]⟩
def initialData (run k : Nat) : Data :=
  ⟨[],[],[],[],[if run % 2 == 0 then [rootMay .u] else entryValues run k] ++ [[],[],[]],[]⟩

def round (enabled : Bool) (run k : Nat) (rows : List Row) (saved : List Saved) (complete : List Ap) (services : List (Ap × Nat)) (d : Data) : Data := Id.run do
  let back := run % 2 == 0
  let mut state := d
  for j in List.range 3 do
    let mut out := state.offers[j+1]!
    for v in state.offers[j]! do
      let a := asInput back k v
      state := {state with domains := (state.domains ++ [a]).eraseDups}
      let replies := actualReplies enabled run k rows saved (complete ++ state.complete) (services ++ state.services) state.closed state.raw a v.h
      out := out ++ (if back then replies else replies.filterMap consumeH)
    state := {state with offers := state.offers.set (j+1) (normalizeContinuation enabled back out)}
  let fresh := candidates run k back rows saved state.domains
  let raw := (state.raw ++ fresh).eraseDups
  return {state with raw := raw,complete := (state.complete ++ certify run k rows saved state.domains raw).eraseDups, services := (state.services ++ certifyMarks run k rows saved state.domains raw).eraseDups, closed := (state.closed ++ certifyClosed run k rows saved state.domains).eraseDups}

-- Exact pure stages of round. These helpers factor evaluation only.
def deliverAt (enabled : Bool) (run k : Nat) (rows : List Row) (saved : List Saved)
    (complete : List Ap) (services : List (Ap × Nat)) (j : Nat) (d : Data) : Data := Id.run do
  let back := run % 2 == 0
  let mut state := d
  let mut out := state.offers[j+1]!
  for v in state.offers[j]! do
    let a := asInput back k v
    state := {state with domains := (state.domains ++ [a]).eraseDups}
    let replies := actualReplies enabled run k rows saved (complete ++ state.complete) (services ++ state.services) state.closed state.raw a v.h
    out := out ++ (if back then replies else replies.filterMap consumeH)
  return {state with offers := state.offers.set (j+1) (normalizeContinuation enabled back out)}

def publishAt (run k : Nat) (rows : List Row) (saved : List Saved) (d : Data) : Data :=
  let raw := (d.raw ++ candidates run k (run % 2 == 0) rows saved d.domains).eraseDups
  {d with raw := raw,complete := (d.complete ++ certify run k rows saved d.domains raw).eraseDups, services := (d.services ++ certifyMarks run k rows saved d.domains raw).eraseDups, closed := (d.closed ++ certifyClosed run k rows saved d.domains).eraseDups}

theorem factoring_the_three_deliveries_is_exact (enabled : Bool) (run k : Nat)
    (rows : List Row) (saved : List Saved) (complete : List Ap) (services : List (Ap × Nat)) (d : Data) :
    round enabled run k rows saved complete services d = publishAt run k rows saved
      (deliverAt enabled run k rows saved complete services 2
        (deliverAt enabled run k rows saved complete services 1 (deliverAt enabled run k rows saved complete services 0 d))) := by rfl

def analyze (enabled : Bool) (fuel run k : Nat) (rows : List Row) (saved : List Saved) (complete : List Ap) (services : List (Ap × Nat)) : Data :=
  fuel.rec (initialData run k) (fun _ d => round enabled run k rows saved complete services d)

def outputRows (d : Data) : List Row :=
  (d.raw.filterMap fun e => if e.2.demand then some ⟨normalGuidance e.2.ap,normalGuidance e.1⟩ else none).eraseDups

def outputSaved (back : Bool) (old : List Saved) (d : Data) : List Saved :=
  (old ++ (canonicalEdges d.raw).filterMap (fun (e : Edge) => if e.2.demand then none
    else some (⟨if back then reverseSaved e else e,back⟩ : Saved))).eraseDups

def initial : State := ⟨[],[],[],[],true,false,false,emptyData⟩
def quiet (report : Bool) (saved : List Saved) (complete : List Ap) (services : List (Ap × Nat)) : State := ⟨[],saved,complete,services,false,false,report,emptyData⟩
def limit (run : Nat) : Nat := max 1 (run-1)

def entryBackValues (_run _k : Nat) (d : Data) : List Value :=
  d.offers.getLast!

def producerHit (run k : Nat) (d : Data) : Bool := (entryBackValues run k d).any fun v =>
  v.ap.mark == originalSource.ap.mark &&
    ((match dropHead v.ap.path originalSource.ap.path with
      | some rest => admits v.ap.tail v.ap.e rest
      | none => false) ||
      (originalSource.ap.tail == .must && (dropHead originalSource.ap.path v.ap.path).isSome))

def anyTarget (enabled : Bool) (run k : Nat) (old : State) : Bool :=
  UniformSticky.seenDemand (fun d => d.offers.getLast!.any (·.demand))
    (round enabled run k old.rows old.saved old.complete old.services) 8 (initialData run k)

def stepWithLimit (enabled : Bool) (run k : Nat) (old : State) : State :=
  let back := run % 2 == 0
  let active := if back then old.observationActive else old.sourceAllowed
  if !active then quiet old.report old.saved old.complete old.services else
  let data := analyze enabled 8 run k old.rows old.saved old.complete old.services
  let rows := outputRows data
  let saved := outputSaved back old.saved data
  let complete := (old.complete ++ data.complete).eraseDups
  let services := ((old.services ++ data.services).eraseDups).filter
    (fun item => !complete.any (fun q => decide (q=item.1)))
  if back then ⟨rows,saved,complete,services,producerHit run k data,false,old.report,data⟩ else
    ⟨rows,saved,complete,services,old.sourceAllowed,anyTarget enabled run k old,
      old.report || data.offers.getLast!.any (fun v => !v.demand),data⟩
def step (enabled : Bool) (run : Nat) (old : State) : State :=
  stepWithLimit enabled run (limit run) old

def history (enabled : Bool) : Nat → State
  | 0 => initial
  | n+1 => step enabled (n+1) (history enabled n)

def stopped (run : Nat) (s : State) : Bool := run % 2 == 1 && s.rows.isEmpty && !s.observationActive

theorem quiet_never_restarts (enabled : Bool) (run : Nat) (report : Bool) (saved : List Saved) (complete : List Ap) (services : List (Ap × Nat)) :
    step enabled run (quiet report saved complete services) = quiet report saved complete services := by simp [step,stepWithLimit,quiet]

theorem ordinary_read_consumes_the_known_h_prefix :
    consumeH (value p [h] .may .u)=some (rootMay .u) := by decide

end BoundOldField
