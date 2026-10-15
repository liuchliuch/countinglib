import Paper2.Charge
import Paper2.ChargeSemigroup
import Mathlib.Data.Fintype.Sigma

/-!
Actual finite tensor products for the arithmetic stage of Lemma 4.1.
The coefficients are products of input coefficients, with a separate copy for
every natural multiplicity. No negative tensor powers or formal linear sums
are used. This module establishes the tensor tables and their supported charge;
conversion into an ordered open-network term is a separate interface.
-/
namespace Paper2
open scoped BigOperators

section SigmaCharge
variable {ι : Type*} {κ : ι → Type*} [Fintype ι] [∀ i, Fintype (κ i)]

lemma doubledCharge_sigma (x : (Σ i, κ i) → Bool) :
    doubledCharge x = ∑ i, doubledCharge (fun j : κ i => x ⟨i, j⟩) := by
  simp only [doubledCharge_eq_sum]
  exact Fintype.sum_sigma _

lemma even_card_sigma (heven : ∀ i, Even (Fintype.card (κ i))) :
    Even (Fintype.card (Σ i, κ i)) := by
  rw [Fintype.card_sigma]
  exact even_iff_two_dvd.mpr (Finset.dvd_sum (fun i _ => (even_iff_two_dvd.mp (heven i))))

lemma halfCharge_sigma (heven : ∀ i, Even (Fintype.card (κ i)))
    (x : (Σ i, κ i) → Bool) :
    halfCharge x = ∑ i, halfCharge (fun j : κ i => x ⟨i, j⟩) := by
  have htotal := twice_halfCharge (even_card_sigma heven) x
  have hlocal : ∀ i, doubledCharge (fun j : κ i => x ⟨i, j⟩) =
      2 * halfCharge (fun j : κ i => x ⟨i, j⟩) :=
    fun i => (twice_halfCharge (heven i) _).symm
  rw [doubledCharge_sigma, Finset.sum_congr rfl (fun i _ => hlocal i),
    ← Finset.mul_sum] at htotal
  omega
end SigmaCharge

namespace Tensor
variable {K ι : Type*} {κ : ι → Type*} [Fintype ι]

/-- A literal tensor product of finitely many independently ordered port blocks. -/
def piTensor [CommMonoid K] (f : (i : ι) → Tensor K (κ i)) :
    Tensor K (Σ i, κ i) := fun x => ∏ i, f i (fun j => x ⟨i, j⟩)

@[simp] lemma piTensor_apply [CommMonoid K] (f : (i : ι) → Tensor K (κ i))
    (x : (Σ i, κ i) → Bool) :
    piTensor f x = ∏ i, f i (fun j => x ⟨i, j⟩) := rfl

lemma piTensor_ne_zero [CommMonoidWithZero K] [NoZeroDivisors K] [Nontrivial K]
    (f : (i : ι) → Tensor K (κ i)) (x : (Σ i, κ i) → Bool) :
    piTensor f x ≠ 0 ↔ ∀ i, f i (fun j => x ⟨i, j⟩) ≠ 0 := by
  simp [piTensor, Finset.prod_ne_zero_iff]

lemma piTensor_halfChargeDivisible [CommMonoidWithZero K] [NoZeroDivisors K] [Nontrivial K]
    [∀ i, Fintype (κ i)] (f : (i : ι) → Tensor K (κ i)) (d : ℤ)
    (heven : ∀ i, Even (Fintype.card (κ i)))
    (hdiv : ∀ i, HalfChargeDivisible (f i) d) :
    HalfChargeDivisible (piTensor f) d := by
  intro x hx
  rw [halfCharge_sigma heven]
  apply Finset.dvd_sum
  intro i _
  exact hdiv i _ ((piTensor_ne_zero f x).mp hx i)

end Tensor

namespace ChargeProducts
variable {K ι : Type*} [Fintype ι]

/-- One independent occurrence for each copy of each available signature. -/
abbrev Copies (n : ι → ℕ) := Σ i, Fin (n i)

/-- The complete port type retains the occurrence and local port indices. -/
abbrev Ports (n r : ι → ℕ) := Σ i : Copies n, Fin (r i.1)

/-- A repeated finite product of genuine signature coefficients. -/
def table [CommMonoid K] (n r : ι → ℕ) (f : (i : ι) → Signature K (r i)) :
    Tensor K (Ports n r) := Tensor.piTensor (fun i : Copies n => f i.1)

/-- Repeat the selected supported word independently in every copy. -/
def word (n r : ι → ℕ) (x : (i : ι) → Fin (r i) → Bool) : Ports n r → Bool :=
  fun p => x p.1.1 p.2

lemma word_charge (n r : ι → ℕ) (heven : ∀ i, Even (r i))
    (x : (i : ι) → Fin (r i) → Bool) :
    halfCharge (word n r x) = ∑ i, (n i : ℤ) * halfCharge (x i) := by
  rw [halfCharge_sigma (fun i => by simpa using heven i.1)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ _ : Fin (n i), halfCharge (x i)) = (n i : ℤ) * halfCharge (x i)
  simp [nsmul_eq_mul]

lemma word_supported [CommMonoidWithZero K] [NoZeroDivisors K] [Nontrivial K]
    (n r : ι → ℕ) (f : (i : ι) → Signature K (r i))
    (x : (i : ι) → Fin (r i) → Bool) (hx : ∀ i, f i (x i) ≠ 0) :
    table n r f (word n r x) ≠ 0 := by
  apply (Tensor.piTensor_ne_zero _ _).mpr
  intro i
  exact hx i.1

lemma table_divisible [CommMonoidWithZero K] [NoZeroDivisors K] [Nontrivial K]
    (n r : ι → ℕ) (f : (i : ι) → Signature K (r i)) (d : ℤ)
    (heven : ∀ i, Even (r i))
    (hf : ∀ i, Tensor.HalfChargeDivisible (f i) d) :
    Tensor.HalfChargeDivisible (table n r f) d := by
  apply Tensor.piTensor_halfChargeDivisible
  · intro i
    simpa using heven i.1
  · intro i
    exact hf i.1

/-- A natural multiplicity combination yields an actual nonzero tensor entry
of exactly that charge. This is the source's tensor-product use of Bézout. -/
theorem supported_charge_combination [CommMonoidWithZero K] [NoZeroDivisors K] [Nontrivial K]
    (n r : ι → ℕ) (f : (i : ι) → Signature K (r i))
    (x : (i : ι) → Fin (r i) → Bool) (c : ι → ℤ) (z : ℤ)
    (heven : ∀ i, Even (r i)) (hsupport : ∀ i, f i (x i) ≠ 0)
    (hcharge : ∀ i, halfCharge (x i) = c i)
    (hsum : ∑ i, (n i : ℤ) * c i = z) :
    ∃ y : Ports n r → Bool, table n r f y ≠ 0 ∧ halfCharge y = z := by
  refine ⟨word n r x, word_supported n r f x hsupport, ?_⟩
  rw [word_charge n r heven x]
  simpa only [hcharge] using hsum

end ChargeProducts
end Paper2
