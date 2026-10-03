import Std

namespace BaseOnly

abbrev StaticId := Nat
abbrev FieldId := Nat
abbrev TerminalId := Nat

structure PrecisePath where
  static : Option StaticId
  fields : List FieldId
  terminal : TerminalId
deriving Repr, DecidableEq

structure Access where
  static : Option StaticId
  field : Option FieldId
  terminal : TerminalId
deriving Repr, DecidableEq

def project (fieldSensitive : Bool) (path : PrecisePath) : Access :=
  {
    static := path.static
    field := if fieldSensitive then path.fields.head? else none
    terminal := path.terminal
  }

def Access.denotes (access : Access) (path : PrecisePath) : Bool :=
  access.static == path.static &&
    access.terminal == path.terminal &&
    match access.field with
    | none => true
    | some field => path.fields.head? == some field

def retainedFieldCount (access : Access) : Nat :=
  access.field.toList.length

theorem project_denotes_precise_path
    (fieldSensitive : Bool) (path : PrecisePath) :
    (project fieldSensitive path).denotes path = true := by
  cases path with
  | mk static fields terminal =>
      cases fieldSensitive <;> cases fields <;> simp [project, Access.denotes]

theorem projection_is_constructive
    (fieldSensitive : Bool) (path : PrecisePath) :
    ∃ access, access = project fieldSensitive path ∧ access.denotes path = true := by
  exact ⟨project fieldSensitive path, rfl, project_denotes_precise_path fieldSensitive path⟩

theorem projection_retains_at_most_one_field
    (fieldSensitive : Bool) (path : PrecisePath) :
    retainedFieldCount (project fieldSensitive path) ≤ 1 := by
  cases fieldSensitive <;> simp [project, retainedFieldCount]

theorem field_insensitive_projection_drops_field_identity
    (path : PrecisePath) :
    (project false path).field = none := by
  rfl

theorem field_sensitive_projection_retains_outer_field
    (path : PrecisePath) :
    (project true path).field = path.fields.head? := by
  rfl

end BaseOnly
