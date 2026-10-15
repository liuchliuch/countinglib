import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite Boolean witness counting

The basic counting API is extracted from `Holant.Complexity.WitnessCounting`
(`holant-binary-disequality-lean`, commit
`ec3e598e380c57e1c4d1a3c73a4ad1b4f7eed711`). It has no machine dependency:
finite cardinality identities do not assert complexity bounds. The unique-padding
lemmas extend that API and explicitly exclude arbitrary ignored padding bits.
-/

namespace Counting.Foundation

open scoped BigOperators

/-- The number of accepted elements of a finite witness type. -/
def countAccepted {W : Type*} [Fintype W] (accept : W → Bool) : Nat :=
  ∑ w, if accept w then 1 else 0

/-- The finite indicator sum is exactly the cardinality of accepted witnesses.
This semantic theorem is independent of machines and source-specific adapters. -/
theorem countAccepted_eq_card {W : Type*} [Fintype W] (accept : W → Bool) :
    countAccepted accept = Fintype.card {w : W // accept w = true} := by
  rw [Fintype.card_subtype]
  simp only [countAccepted, Finset.card_eq_sum_ones, Finset.sum_filter]

@[simp] theorem countAccepted_false {W : Type*} [Fintype W] :
    countAccepted (fun _ : W => false) = 0 := by simp [countAccepted]

@[simp] theorem countAccepted_true {W : Type*} [Fintype W] :
    countAccepted (fun _ : W => true) = Fintype.card W := by simp [countAccepted]

/-- Pointwise equal acceptance predicates have equal counts. -/
theorem countAccepted_congr {W : Type*} [Fintype W] {a b : W → Bool}
    (h : ∀ w, a w = b w) : countAccepted a = countAccepted b := by
  simp only [countAccepted, h]

theorem countAccepted_le {W : Type*} [Fintype W] (accept : W → Bool) :
    countAccepted accept ≤ Fintype.card W := by
  calc
    countAccepted accept ≤ ∑ _w : W, 1 := by
      apply Finset.sum_le_sum
      intro w _
      cases accept w <;> simp
    _ = Fintype.card W := by simp

/-- A parsimonious bijection preserves the number of accepted witnesses. -/
theorem countAccepted_equiv {W V : Type*} [Fintype W] [Fintype V]
    (e : W ≃ V) (accept : V → Bool) :
    countAccepted (fun w => accept (e w)) = countAccepted accept :=
  e.sum_comp (fun v => if accept v then 1 else 0)

/-- Bijections may relate predicates on different witness presentations. -/
theorem countAccepted_bijection {W V : Type*} [Fintype W] [Fintype V]
    (e : W ≃ V) (a : W → Bool) (b : V → Bool) (h : ∀ w, a w = b (e w)) :
    countAccepted a = countAccepted b := by
  calc
    countAccepted a = countAccepted (fun w => b (e w)) := countAccepted_congr h
    _ = countAccepted b := countAccepted_equiv e b

/-- Ignoring an independent witness component multiplies the count by its
cardinality. In particular, freely adding bits does not preserve counts. -/
theorem countAccepted_ignored_product {W V : Type*} [Fintype W] [Fintype V]
    (accept : W → Bool) :
    countAccepted (fun w : W × V => accept w.1) = countAccepted accept * Fintype.card V := by
  unfold countAccepted
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  change (∑ _v : V, if accept w then 1 else 0) =
    (if accept w then 1 else 0) * Fintype.card V
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact Nat.mul_comm _ _

/-- Independent conjunction multiplies accepting counts. -/
theorem countAccepted_product {W V : Type*} [Fintype W] [Fintype V]
    (a : W → Bool) (b : V → Bool) :
    countAccepted (fun w : W × V => a w.1 && b w.2) = countAccepted a * countAccepted b := by
  unfold countAccepted
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  change (if a w && b v then 1 else 0) = (if a w then 1 else 0) * (if b v then 1 else 0)
  cases a w <;> cases b v <;> rfl

@[simp] theorem countAccepted_singleton {W : Type*} [Fintype W] [DecidableEq W]
    (w₀ : W) : countAccepted (fun w => decide (w = w₀)) = 1 := by
  simp [countAccepted]

/-- An independent padding predicate with exactly one accepted filler is
parsimonious. This hypothesis is about finite cardinality, not time complexity. -/
theorem countAccepted_unique_padding {W V : Type*} [Fintype W] [Fintype V]
    (accept : W → Bool) (padding : V → Bool) (h : countAccepted padding = 1) :
    countAccepted (fun w : W × V => accept w.1 && padding w.2) = countAccepted accept := by
  rw [countAccepted_product, h, Nat.mul_one]

/-- Requiring a specified filler preserves the count. -/
theorem countAccepted_fixed_padding {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq V] (accept : W → Bool) (filler : V) :
    countAccepted (fun w : W × V => accept w.1 && decide (w.2 = filler)) =
      countAccepted accept :=
  countAccepted_unique_padding accept _ (countAccepted_singleton filler)

/-- Ordered Boolean witnesses have exactly `n` bits. -/
def witnessCount (n : Nat) (accept : List Bool → Bool) : Nat :=
  countAccepted (fun w : Fin n → Bool => accept (List.ofFn w))

@[simp] theorem witnessCount_false (n : Nat) : witnessCount n (fun _ => false) = 0 := by
  simp [witnessCount]

@[simp] theorem witnessCount_true (n : Nat) : witnessCount n (fun _ => true) = 2 ^ n := by
  simp [witnessCount]

theorem witnessCount_le (n : Nat) (accept : List Bool → Bool) :
    witnessCount n accept ≤ 2 ^ n := by
  simpa [witnessCount] using
    countAccepted_le (fun w : Fin n → Bool => accept (List.ofFn w))

/-- Split an exact-length witness into an ordered prefix and suffix. -/
theorem witnessCount_append (n k : Nat) (accept : List Bool → Bool) :
    witnessCount (n + k) accept =
      countAccepted (fun w : (Fin n → Bool) × (Fin k → Bool) =>
        accept (List.ofFn w.1 ++ List.ofFn w.2)) := by
  symm
  simpa [witnessCount, Fin.appendEquiv, List.ofFn_fin_append] using
    countAccepted_equiv (Fin.appendEquiv n k)
      (fun w : Fin (n + k) → Bool => accept (List.ofFn w))

/-- Acceptance predicate for a prefix followed by exactly `k` false padding bits.
The enclosing `witnessCount (n + k)` supplies the total-length restriction. -/
def falsePadding (n k : Nat) (accept : List Bool → Bool) (w : List Bool) : Bool :=
  accept (w.take n) && decide (w.drop n = List.replicate k false)

/-- Appending a uniquely determined all-false suffix preserves every count,
including zero-length witnesses and zero-length padding. -/
theorem witnessCount_falsePadding (n k : Nat) (accept : List Bool → Bool) :
    witnessCount (n + k) (falsePadding n k accept) = witnessCount n accept := by
  rw [witnessCount_append]
  calc
    countAccepted (fun w : (Fin n → Bool) × (Fin k → Bool) =>
        falsePadding n k accept (List.ofFn w.1 ++ List.ofFn w.2)) =
      countAccepted (fun w : (Fin n → Bool) × (Fin k → Bool) =>
        accept (List.ofFn w.1) && decide (w.2 = fun _ => false)) := by
      apply countAccepted_congr
      intro w
      simp [falsePadding, ← List.ofFn_const, List.ofFn_inj]
    _ = witnessCount n accept :=
      countAccepted_fixed_padding (fun w : Fin n → Bool => accept (List.ofFn w))
        (fun _ : Fin k => false)

/-- In contrast, an ignored `k`-bit suffix contributes the factor `2 ^ k`. -/
theorem witnessCount_ignored_padding (n k : Nat) (accept : List Bool → Bool) :
    witnessCount (n + k) (fun w => accept (w.take n)) = witnessCount n accept * 2 ^ k := by
  rw [witnessCount_append]
  calc
    countAccepted (fun w : (Fin n → Bool) × (Fin k → Bool) =>
        accept ((List.ofFn w.1 ++ List.ofFn w.2).take n)) =
      countAccepted (fun w : (Fin n → Bool) × (Fin k → Bool) => accept (List.ofFn w.1)) := by
      apply countAccepted_congr
      intro w
      simp
    _ = witnessCount n accept * 2 ^ k := by
      simpa [witnessCount] using
        countAccepted_ignored_product (V := Fin k → Bool)
          (fun w : Fin n → Bool => accept (List.ofFn w))

end Counting.Foundation
