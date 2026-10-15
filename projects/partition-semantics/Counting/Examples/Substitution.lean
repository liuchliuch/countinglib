import Counting.Gadget.Composition

/-!
# A concrete client of arbitrary occurrence substitution

A binary Boolean table has row sums `3` and `4`. Its unary presentation sums one
hidden Boolean variable. A source instance repeats that unary occurrence and
also retains an isolated original hidden variable. Substitution must therefore
create two fresh summed variables and retain the original one.

The local table and source values use small kernel-checked finite calculations;
the compiled partition value follows from the generic substitution theorem,
without evaluating the compiled assignment space.
-/

namespace Counting.Examples.SubstitutionClient

open Counting.Model Counting.Gadget

/-- A genuinely binary table: the hidden port affects both boundary rows. -/
def baseLanguage : Language Bool Nat Unit where
  arity _ := 2
  value _ x := if x 0 then (if x 1 then 3 else 1) else (if x 1 then 2 else 1)

/-- The table obtained by summing the second port of `baseLanguage`. -/
def sourceLanguage : Language Bool Nat Unit where
  arity _ := 1
  value _ x := if x 0 then 4 else 3

/-- Ordered ports are boundary first, hidden second. -/
def baseOccurrence : Occurrence baseLanguage (Fin 1 ⊕ Fin 1) :=
  ⟨(), fun i => if i.val = 0 then Sum.inl 0 else Sum.inr 0⟩

/-- One actual base-language factor with one hidden Boolean variable. -/
def unaryGadget : Presentation baseLanguage (Fin 1) :=
  ⟨1, ⟨[baseOccurrence]⟩⟩

/-- The sole source label is implemented by the unary gadget. -/
def gadgets : Substitution.Gadgets baseLanguage sourceLanguage := fun _ => unaryGadget

/-- Four table-entry evaluations establish the local realization equation. -/
theorem gadgets_realize : Substitution.Realizes gadgets := by
  unfold Substitution.Realizes
  decide

/-- The original hidden variable never occurs in this source scope. -/
def sourceOccurrence : Occurrence sourceLanguage (Fin 1 ⊕ Fin 1) :=
  ⟨(), fun _ => Sum.inl 0⟩

/-- Multiplicity is literal list multiplicity; the original hidden variable is isolated. -/
def repeatedSource : OpenInstance sourceLanguage (Fin 1) (Fin 1) :=
  ⟨[sourceOccurrence, sourceOccurrence]⟩

theorem source_scope_avoids_hidden (i : Fin (sourceLanguage.arity ())) :
    sourceOccurrence.scope i = Sum.inl 0 := rfl

/-- Each of the two occurrences supplies its own one-variable summation block. -/
theorem two_fresh_hidden_variables :
    (Substitution.expand gadgets repeatedSource).hidden = 2 := by
  rw [Substitution.hidden_expand]
  rfl

/-- Neither repeated occurrence is lost by the compiler. -/
theorem two_compiled_occurrences :
    (Substitution.compile gadgets repeatedSource).occurrences.length = 2 := by
  rw [Substitution.occurrences_length_compile]
  rfl

/-- The compiled hidden type includes the isolated original variable and both fresh ones. -/
theorem three_total_hidden_variables :
    Fintype.card (Fin 1 ⊕ Fin (Substitution.expand gadgets repeatedSource).hidden) = 3 := by
  simp [two_fresh_hidden_variables]

/-- This equality is an application of the reusable theorem, not a finite recomputation. -/
theorem repeated_partition_preserved (a : Fin 1 → Bool) :
    (Substitution.compile gadgets repeatedSource).partition a =
      repeatedSource.partition a :=
  Substitution.partition_compile gadgets gadgets_realize repeatedSource a

/-- The isolated original variable contributes a factor of two after squaring the row sum. -/
theorem source_partition (a : Fin 1 → Bool) :
    repeatedSource.partition a = 2 * (if a 0 then 4 else 3) ^ 2 := by
  revert a
  decide

/-- The complete compiled table is `18, 32`, retaining all three summation variables. -/
theorem compiled_partition (a : Fin 1 → Bool) :
    (Substitution.compile gadgets repeatedSource).partition a =
      2 * (if a 0 then 4 else 3) ^ 2 := by
  rw [repeated_partition_preserved, source_partition]

theorem compiled_false :
    (Substitution.compile gadgets repeatedSource).partition (fun _ => false) = 18 := by
  rw [compiled_partition]
  decide

theorem compiled_true :
    (Substitution.compile gadgets repeatedSource).partition (fun _ => true) = 32 := by
  rw [compiled_partition]
  decide

end Counting.Examples.SubstitutionClient
