import Holant.Complexity.ConstantMachine
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

/-!
# Finite-machine polynomial witness counting

The public interface counts a finite subtype of accepted Boolean witnesses. Its
verifier is a real finite TM2 whose polynomial runtime is proved against the
transition semantics, using the faithful tagged input/witness encoding. A witness
has exactly the prescribed length; there are no unspecified ignored padding bits.

This is a witness presentation of natural-valued #P. An equivalence with an
accepting-path presentation is a separate theorem and is not asserted here.
-/

namespace Counting.Complexity

open Computability

/-- A natural-valued counting function represented by a polynomial-length Boolean
witness and a concrete polynomial-time finite machine. The machine's time is
measured on the full encoded pair, not just its instance component. -/
structure SharpPWitness {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ)
    (f : α → ℕ) where
  witnessLength : Polynomial ℕ
  accept : α × List Bool → Bool
  verifier : Holant.Complexity.PolyTime
    (encodingProd ea (encodingList Bool)) (Holant.Complexity.taggedBoolEncoding Γ) accept
  counts : ∀ a, f a = Fintype.card
    {w : Fin (witnessLength.eval (ea.encode a).length) → Bool //
      accept (a, List.ofFn w) = true}

/-- Existence of a witness counter with a proved finite-machine polynomial bound. -/
def InSharpP {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ) (f : α → ℕ) : Prop :=
  Nonempty (SharpPWitness ea f)

/-- There are at most as many accepted witnesses as Boolean strings of the exact
polynomial length. -/
theorem SharpPWitness.count_le {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ}
    {f : α → ℕ} (w : SharpPWitness ea f) (a : α) :
    f a ≤ 2 ^ (w.witnessLength.eval (ea.encode a).length) := by
  rw [w.counts]
  simpa using Fintype.card_subtype_le
    (fun v : Fin (w.witnessLength.eval (ea.encode a).length) → Bool =>
      w.accept (a, List.ofFn v) = true)

/-- An accepting constant machine counts every string. Its implementation pops the
full input stack and writes `true` in exactly input length plus one transitions. -/
noncomputable def allWitnesses {α Γ : Type} [Fintype Γ]
    (ea : Encoding α Γ) (p : Polynomial ℕ) :
    SharpPWitness ea (fun a => 2 ^ p.eval (ea.encode a).length) where
  witnessLength := p
  accept _ := true
  verifier := Holant.Complexity.constantBoolPolyTime
    (encodingProd ea (encodingList Bool)) true
  counts _ := by simp

/-- A concrete rejecting machine realizes the zero counting function. -/
noncomputable def noWitnesses {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ) :
    SharpPWitness ea (fun _ => 0) where
  witnessLength := 0
  accept _ := false
  verifier := Holant.Complexity.constantBoolPolyTime
    (encodingProd ea (encodingList Bool)) false
  counts _ := by simp

/-- Exponentially many branches arise from a linear-time accepting verifier, even
though the count itself is not produced by that verifier. -/
theorem exponential_inSharpP {α Γ : Type} [Fintype Γ]
    (ea : Encoding α Γ) (p : Polynomial ℕ) :
    InSharpP ea (fun a => 2 ^ p.eval (ea.encode a).length) :=
  ⟨allWitnesses ea p⟩

theorem zero_inSharpP {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ) :
    InSharpP ea (fun _ => 0) := ⟨noWitnesses ea⟩

/-- An accepting verifier with no witness bits counts the unique empty witness. -/
theorem one_inSharpP {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ) :
    InSharpP ea (fun _ => 1) := by
  simpa using exponential_inSharpP ea (0 : Polynomial ℕ)

end Counting.Complexity
