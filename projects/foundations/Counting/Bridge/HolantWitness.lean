import Holant.Complexity.WitnessCounting
import Counting.Foundation.Witness
import Counting.Complexity.SharpP

/-!
# Bridge from the locked Holant witness interface

The source-facing declarations are the unmodified
`Holant.Complexity.WitnessCounting` at commit
`ec3e598e380c57e1c4d1a3c73a4ad1b4f7eed711` (the same source blob also occurs
in the locked full Holant release). The new interface represents counts by finite
subtypes; the original interface sums Boolean acceptance indicators. Their
identification below transports the complete machine witness in both directions,
including its original timed-run proof and exact witness-length polynomial.

No machine-model or accepting-path equivalence is claimed by this bridge.
-/

namespace Counting.Bridge.HolantWitness

open Computability

/-- The extracted finite sum retains the original Holant counting semantics. -/
theorem holant_countAccepted_eq_countAccepted {W : Type*} [Fintype W]
    (accept : W → Bool) :
    Holant.Complexity.countAccepted accept = Foundation.countAccepted accept := rfl

/-- A sum of Boolean acceptance indicators is the cardinality of the accepted
subtype. This is the semantic change between the two witness interfaces. -/
theorem holant_countAccepted_eq_card {W : Type*} [Fintype W]
    (accept : W → Bool) :
    Holant.Complexity.countAccepted accept = Fintype.card {w : W // accept w = true} := by
  rw [holant_countAccepted_eq_countAccepted]
  exact Foundation.countAccepted_eq_card accept

/-- Exact-length Boolean witnesses keep their original ordered list encoding. -/
theorem holant_witnessCount_eq_card (n : ℕ) (accept : List Bool → Bool) :
    Holant.Complexity.witnessCount n accept =
      Fintype.card {w : Fin n → Bool // accept (List.ofFn w) = true} :=
  holant_countAccepted_eq_card _

/-- Import an original witness counter without changing its machine, runtime
polynomial, accepted predicate, or prescribed witness length. -/
def ofHolantSharpPWitness {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ}
    {f : α → ℕ} (w : Holant.Complexity.SharpPWitness ea f) :
    Complexity.SharpPWitness ea f where
  witnessLength := w.witnessLength
  accept := w.accept
  verifier := w.verifier
  counts a := (w.counts a).trans (holant_witnessCount_eq_card _ _)

/-- Export a new witness counter to the original interface, preserving the
concrete machine and its timed correctness proof. -/
def toHolantSharpPWitness {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ}
    {f : α → ℕ} (w : Complexity.SharpPWitness ea f) :
    Holant.Complexity.SharpPWitness ea f where
  witnessLength := w.witnessLength
  accept := w.accept
  verifier := w.verifier
  counts a := (w.counts a).trans
    (holant_witnessCount_eq_card (w.witnessLength.eval (ea.encode a).length)
      (fun v => w.accept (a, v))).symm

/-- Import followed by export preserves all original witness data. -/
@[simp] theorem toHolant_ofHolant {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ}
    {f : α → ℕ} (w : Holant.Complexity.SharpPWitness ea f) :
    toHolantSharpPWitness (ofHolantSharpPWitness w) = w := by
  cases w
  rfl

/-- Export followed by import preserves all new witness data. -/
@[simp] theorem ofHolant_toHolant {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ}
    {f : α → ℕ} (w : Complexity.SharpPWitness ea f) :
    ofHolantSharpPWitness (toHolantSharpPWitness w) = w := by
  cases w
  rfl

/-- The two full witness structures are equivalent, not merely their counts. -/
def holantSharpPWitnessEquiv {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ)
    (f : α → ℕ) :
    Holant.Complexity.SharpPWitness ea f ≃ Complexity.SharpPWitness ea f where
  toFun := ofHolantSharpPWitness
  invFun := toHolantSharpPWitness
  left_inv := toHolant_ofHolant
  right_inv := ofHolant_toHolant

/-- Original Holant witness membership and the new finite-subtype presentation
have exactly the same instances under the same faithful encoding. -/
theorem holant_inSharpP_iff {α Γ : Type} [Fintype Γ] (ea : Encoding α Γ)
    (f : α → ℕ) :
    Holant.Complexity.InSharpP ea f ↔ Complexity.InSharpP ea f := by
  constructor
  · rintro ⟨w⟩
    exact ⟨ofHolantSharpPWitness w⟩
  · rintro ⟨w⟩
    exact ⟨toHolantSharpPWitness w⟩

end Counting.Bridge.HolantWitness
