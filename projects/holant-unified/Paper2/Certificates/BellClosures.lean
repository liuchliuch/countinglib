import Paper2.Bell
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators

/-! Exact closure-query identities in the Bell occurrence reduction. All
pairings are finite bilinear sums, without complex conjugation. -/
namespace Paper2.Bell.Closures

variable {K : Type*} [CommRing K]

def fourPair (H : Signature K 4) (A B : Kernel K) : K :=
  ∑ x : Fin 4 → Bool, H x * (A (x 0) (x 1) * B (x 2) (x 3))

def native12 (H : Signature K 4) : K := fourPair H X X

def native13 (H : Signature K 4) : K :=
  ∑ x : Fin 4 → Bool, H x * (X (x 0) (x 2) * X (x 1) (x 3))

def native14 (H : Signature K 4) : K :=
  ∑ x : Fin 4 → Bool, H x * (X (x 0) (x 3) * X (x 1) (x 2))

/-- Q8.32 lifts to exactly two ordinary native-X closure queries. -/
theorem two_y_queries (H : Signature K 4) :
    fourPair H Y Y = native14 H - native13 H := by
  unfold fourPair native14 native13
  simp_rw [Bell.y_square_closures,mul_sub]
  rw [Finset.sum_sub_distrib]

/-- The denominator-free three-query identity on every EO boundary tensor. -/
theorem two_i_queries (H : Signature K 4)
    (hEO : ∀ x, (x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat ≠ 2 → H x = 0) :
    (2 : K) * fourPair H I I = native13 H + native14 H - native12 H := by
  unfold native12 native13 native14 fourPair
  rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : (x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat = 2
  · have he := Bell.equality_eo_closures (K := K) (x 0) (x 1) (x 2) (x 3) h
    calc
      2 * (H x * (I (x 0) (x 1) * I (x 2) (x 3))) =
          H x * (2 * (I (x 0) (x 1) * I (x 2) (x 3))) := by ring
      _ = _ := by rw [he]; ring
  · rw [hEO x h]
    ring

/-- One I occurrence vanishes on every anti-diagonal binary boundary table. -/
theorem one_i_zero (H : Kernel K) (h00 : H false false = 0) (h11 : H true true = 0) :
    Kernel.pair H I = 0 := by
  simp [Kernel.pair,I,ordered,sign,h00,h11]

def binaryTensor (H G : Kernel K) : Signature K 4 :=
  fun x => H (x 0) (x 1) * G (x 2) (x 3)

theorem sum_word_succ (n : ℕ) (f : (Fin (n + 1) → Bool) → K) :
    (∑ x, f x) = ∑ a : Bool, ∑ y : Fin n → Bool, f (Fin.cons a y) := by
  calc
    (∑ x, f x) = ∑ z : Bool × (Fin n → Bool), f (Fin.cons z.1 z.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
        (fun z => f (Fin.cons z.1 z.2)) f (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type]

theorem sum_word_zero (f : (Fin 0 → Bool) → K) : (∑ x, f x) = f Fin.elim0 := by
  rw [Fintype.sum_unique]
  congr 1

theorem cons_two {n : ℕ} (a : Bool) (y : Fin (n + 2) → Bool) :
    (Fin.cons a y : Fin (n + 3) → Bool) 2 = y 1 := rfl

theorem cons_three {n : ℕ} (a : Bool) (y : Fin (n + 3) → Bool) :
    (Fin.cons a y : Fin (n + 4) → Bool) 3 = y 2 := rfl

/-- A disconnected fixed witness multiplies the desired binary response. -/
theorem binary_tensor_pair (H G A B : Kernel K) :
    fourPair (binaryTensor H G) A B = Kernel.pair H A * Kernel.pair G B := by
  simp only [fourPair,binaryTensor,Kernel.pair,sum_word_succ,sum_word_zero,Fintype.sum_bool,
    Fin.cons_zero,Fin.cons_one,cons_two,cons_three]
  ring

/-- The numerator used to evaluate a single Y is exactly the known witness
response times the requested response. This keeps the denominator explicit. -/
theorem one_y_witness_identity (H G : Kernel K) :
    native14 (binaryTensor H G) - native13 (binaryTensor H G) =
      Kernel.pair G Y * Kernel.pair H Y := by
  rw [←two_y_queries,binary_tensor_pair,mul_comm]

/-- In the vanishing branch the one-occurrence answer is exactly zero. -/
theorem one_y_zero (H : Kernel K) (h : Kernel.pair H Y = 0) :
    Kernel.pair H (fun a b => -Y a b) = 0 := by
  simp only [Kernel.pair,mul_neg,Finset.sum_neg_distrib]
  change -(Kernel.pair H Y) = 0
  rw [h,neg_zero]

end Paper2.Bell.Closures
