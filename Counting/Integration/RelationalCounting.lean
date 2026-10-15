import Counting.Foundation.Witness
import Counting.Model.Basic

/-!
# Relational partition values count satisfying assignments

This is a semantic bridge between the two independently developed library layers.
A Boolean-valued relation family gives a natural-valued indicator language. Its
open partition table is exactly the number of accepted hidden assignments, for
every fixed boundary assignment. The domain need not itself be Boolean.

No machine implementation or complexity bound is claimed by this module.
In particular, this equality alone is not a proof of membership in #P.
-/

namespace Counting.Integration

open Counting.Model

/-- A relation family, with explicitly ordered ports and possibly nullary tables. -/
structure RelationLanguage (D ι : Type) where
  arity : ι → Nat
  holds : (i : ι) → (Fin (arity i) → D) → Bool

namespace RelationLanguage

variable {D ι B H V : Type}

/-- The natural-valued indicator language of a Boolean relation family. -/
def indicator (L : RelationLanguage D ι) : Language D Nat ι where
  arity := L.arity
  value i a := if L.holds i a then 1 else 0

/-- Evaluate satisfaction without using the natural-valued partition function. -/
def acceptsOccurrence (L : RelationLanguage D ι)
    (c : Occurrence L.indicator V) (a : V → D) : Bool :=
  L.holds c.symbol (a ∘ c.scope)

/-- Every occurrence must be satisfied, including repeated and nullary ones. -/
def accepts (L : RelationLanguage D ι)
    (I : OpenInstance L.indicator B H) (a : B → D) (b : H → D) : Bool :=
  I.occurrences.all (fun c => L.acceptsOccurrence c (Sum.elim a b))

/-- Products of indicator tables are the indicator of joint satisfaction. -/
theorem eval_eq_indicator (L : RelationLanguage D ι)
    (I : OpenInstance L.indicator B H) (a : B → D) (b : H → D) :
    I.eval a b = if L.accepts I a b then 1 else 0 := by
  rcases I with ⟨cs⟩
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change c.eval (Sum.elim a b) * (OpenInstance.mk cs).eval a b =
      if L.acceptsOccurrence c (Sum.elim a b) &&
        L.accepts (OpenInstance.mk cs) a b then 1 else 0
    rw [ih]
    change (if L.acceptsOccurrence c (Sum.elim a b) then 1 else 0) *
      (if L.accepts (OpenInstance.mk cs) a b then 1 else 0) = _
    cases L.acceptsOccurrence c (Sum.elim a b) <;>
      cases L.accepts (OpenInstance.mk cs) a b <;> rfl

/-- The partition table of a relational instance is its satisfying-assignment
count. Hidden variables are counted even when they occur in no constraint. -/
theorem partition_eq_countAccepted [Fintype D] [Fintype H] [DecidableEq H]
    (L : RelationLanguage D ι) (I : OpenInstance L.indicator B H) (a : B → D) :
    I.partition a = Foundation.countAccepted (L.accepts I a) := by
  unfold OpenInstance.partition Foundation.countAccepted
  apply Finset.sum_congr rfl
  intro b _
  exact L.eval_eq_indicator I a b

/-- The finite-subtype formulation used by the witness-counting foundation. -/
theorem partition_eq_card_satisfying [Fintype D] [Fintype H] [DecidableEq H]
    (L : RelationLanguage D ι) (I : OpenInstance L.indicator B H) (a : B → D) :
    I.partition a = Fintype.card {b : H → D // L.accepts I a b = true} := by
  rw [L.partition_eq_countAccepted, Foundation.countAccepted_eq_card]

/-- Interpret a list as an ordered Boolean assignment. The default is irrelevant
when counting witnesses of the prescribed length `n`. -/
def acceptsBits {n : Nat} (L : RelationLanguage Bool ι)
    (I : OpenInstance L.indicator B (Fin n)) (a : B → Bool) (bits : List Bool) : Bool :=
  L.accepts I a (fun i => bits[i.val]?.getD false)

/-- For Boolean hidden variables, the same partition value uses the exact-length
ordered witness convention of the complexity foundations. -/
theorem partition_eq_witnessCount (n : Nat) (L : RelationLanguage Bool ι)
    (I : OpenInstance L.indicator B (Fin n)) (a : B → Bool) :
    I.partition a = Foundation.witnessCount n (L.acceptsBits I a) := by
  rw [L.partition_eq_countAccepted]
  apply Foundation.countAccepted_congr
  intro b
  simp [acceptsBits]

/-- An empty relational instance retains all choices for its hidden variables. -/
theorem partition_empty [Fintype D] [Fintype H] [DecidableEq H]
    (L : RelationLanguage D ι) (a : B → D) :
    (OpenInstance.mk [] : OpenInstance L.indicator B H).partition a =
      Fintype.card D ^ Fintype.card H := by
  rw [L.partition_eq_countAccepted]
  change Foundation.countAccepted (fun _ : H → D => true) = _
  simp

/-- Repeating a relational constraint does not add a witness choice. This is
specific to indicators: repeated general weighted factors need not be idempotent. -/
theorem partition_duplicate [Fintype D] [Fintype H] [DecidableEq H]
    (L : RelationLanguage D ι) (c : Occurrence L.indicator (B ⊕ H))
    (cs : List (Occurrence L.indicator (B ⊕ H))) (a : B → D) :
    (OpenInstance.mk (c :: c :: cs) : OpenInstance L.indicator B H).partition a =
      (OpenInstance.mk (c :: cs) : OpenInstance L.indicator B H).partition a := by
  rw [L.partition_eq_countAccepted, L.partition_eq_countAccepted]
  apply Foundation.countAccepted_congr
  intro b
  simp [accepts]

end RelationLanguage
end Counting.Integration
