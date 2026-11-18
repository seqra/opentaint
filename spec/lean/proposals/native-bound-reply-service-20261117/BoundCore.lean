import OriginalReturn
import CompleteClosure
namespace BoundCore
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

-- These are views of existing native context, never a new query/store key.
structure Context where
  inputH : Bool := false
  restored : List Nat := []
  deriving DecidableEq, BEq, Repr

def flag (ctx : Context) (c : Value) : Bool :=
  c.h || ctx.inputH || c.ap.mark.any ctx.restored.contains

def bind (ctx : Context) (c : Value) : Value :=
  {c with ap:={c.ap with base:=AlternatingCondition.p},h:=flag ctx c}

def eligible (q : Seed) : Bool :=
  !q.demand && q.ap.mark.isSome && q.ap.mx.isEmpty &&
    ((q.ap.tail == .exact && q.ap.e.isEmpty) || q.ap.tail == .must)

def focus (raw : List Value) (region : Ap) (ctx : Context) (replyH : Bool) : List Value :=
  raw.filter (fun c => flag ctx c==replyH && ReplyCore.overlaps c.ap region)

-- Reuse actual-data whole coverage; do not require a retained redundant
-- scalar that canonicalization has already covered with NORMAL MUST.
def covers (n x : Value) : Bool :=
  !n.demand && n.h==x.h &&
    (decide (n=x) ||
      (n.ap.base==x.ap.base && n.ap.mark==x.ap.mark && n.ap.mark.isSome &&
       n.ap.mx.isEmpty && x.ap.mx.isEmpty && n.ap.tail==.must &&
       (x.ap.tail==.exact || x.ap.tail==.must || x.ap.tail==.may || x.ap.tail==.ne) &&
       (x.ap.tail==.must || x.ap.e.isEmpty) && UniformActual.regionCovers n.ap x.ap))

-- Native service is already applied NORMAL data of this exact context.
def completeFor (native : List Value) (q : Seed) (raw : List Value)
    (region : Ap) (ctx : Context) (replyH : Bool) : Bool :=
  eligible q && raw.all LayerCore.normalLayer &&
    (focus raw region ctx replyH).all
      (fun c => native.any (fun n => covers n (bind ctx c)))

end BoundCore
