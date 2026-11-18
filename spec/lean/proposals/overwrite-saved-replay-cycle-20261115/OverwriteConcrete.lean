import OverwriteReplay

/- Concrete marked-location paths in the argument-to-return cone.
   A strong write of a fresh unmarked node kills the g subtree. Ordinary
   read/write bindings strip/prepend f.f. This is code semantics, not a
   special rule or a MAY-producing library summary. -/
namespace OverwriteConcrete
set_option linter.unusedSimpArgs false
open NonEmptyPolicy AcyclicMayCycle

def keepG : Path → Option Path
  | [] => some []
  | h :: rest => if h == g then none else some (h :: rest)

def reader (word : Path) : Option Path := do
  let before ← keepG word
  let result ← dropHead [f,f] before
  keepG result

def writer (word : Path) : Option Path := do
  let before ← keepG word
  keepG ([f,f] ++ before)

/-- Exact concretization of the NORMAL writer with shared suffix exclusion g. -/
def storedWriter (word : Path) := (keepG word).map ([f,f] ++ ·)
/-- Exact concretization of the NORMAL reader with shared suffix exclusion g. -/
def storedReader (word : Path) := (dropHead [f,f] word).bind keepG

theorem every_concrete_writer_result_is_the_derived_record (word : Path) :
    writer word = storedWriter word := by
  unfold writer storedWriter
  cases result : keepG word with
  | none => rfl
  | some before =>
    rfl

theorem every_concrete_reader_result_is_the_derived_record (word : Path) :
    reader word = storedReader word := by
  cases word with
  | nil => rfl
  | cons h rest =>
    cases same : h == g with
    | false =>
      have keep : keepG (h :: rest) = some (h :: rest) := by
        change (if h == g then none else some (h :: rest)) = some (h :: rest)
        rw [same]
        rfl
      unfold reader storedReader
      rw [keep]
      rfl
    | true =>
      have eq : h = g := Nat.eq_of_beq_eq_true same
      subst h
      rfl

/-- The branch union is complete for the ordinary returned reference. -/
theorem no_other_input_derived_return_path (word : Path) :
    [reader word,writer word].filterMap id =
      [storedReader word,storedWriter word].filterMap id := by
  rw [every_concrete_reader_result_is_the_derived_record,
      every_concrete_writer_result_is_the_derived_record]
end OverwriteConcrete
#print axioms OverwriteConcrete.every_concrete_writer_result_is_the_derived_record
#print axioms OverwriteConcrete.every_concrete_reader_result_is_the_derived_record
#print axioms OverwriteConcrete.no_other_input_derived_return_path
