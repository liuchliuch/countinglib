import Paper2.HeightOne.Dihedral.QuaternaryProduct
import Paper2.HeightOne.PhaseCards.Complement
import Paper2.HeightTwo

/-! Exact inverse-Walsh formulas used in the cyclic four-port closure.
The coefficient tables here are analytic expressions, not extra signatures
declared realizable.  Actual port attachments are proved in a separate module.
-/
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhaseCards Dihedral
open scoped BigOperators

def balancedWalsh (p : AlgebraicComplex) (sigma : Fin 3 → AlgebraicComplex) :
    Signature AlgebraicComplex 4 := fun x =>
  p * (point (fun _ => false) x + point (fun _ => true) x) +
    ∑ i : Fin 3, sigma i * (point (centralWord i (fun _ => false)) x +
      point (flipAll (centralWord i (fun _ => false))) x)

lemma action_point (M : Kernel AlgebraicComplex) (a x : Fin 4 → Bool) :
    action M (point a) x = ∏ i : Fin 4, M (x i) (a i) := by
  classical
  simp [action, point]

lemma action_add (M : Kernel AlgebraicComplex)
    (f g : Signature AlgebraicComplex 4) : action M (f + g) = action M f + action M g := by
  funext x
  simp [action, Finset.sum_add_distrib, mul_add]

lemma action_scalar (M : Kernel AlgebraicComplex) (c : AlgebraicComplex)
    (f : Signature AlgebraicComplex 4) :
    action M (fun x => c * f x) = fun x => c * action M f x := by
  funext x
  simp only [action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma action_balancedWalsh (p : AlgebraicComplex) (sigma : Fin 3 → AlgebraicComplex)
    (x : Fin 4 → Bool) :
    action walsh (balancedWalsh p sigma) x =
      p * ((∏ i : Fin 4, walsh (x i) false) + (∏ i : Fin 4, walsh (x i) true)) +
      ∑ j : Fin 3, sigma j *
        ((∏ i : Fin 4, walsh (x i) (centralWord j (fun _ => false) i)) +
         (∏ i : Fin 4, walsh (x i) (flipAll (centralWord j (fun _ => false)) i))) := by
  classical
  simp only [balancedWalsh, action, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [← mul_assoc]
  rw [Finset.sum_comm]
  simp [point, mul_comm, mul_left_comm, mul_assoc, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

lemma inverseWalsh_balanced_zero (p : AlgebraicComplex) (sigma : Fin 3 → AlgebraicComplex) :
    action walsh (balancedWalsh p sigma) (fun _ => false) =
      2 * (p + ∑ j, sigma j) := by
  rw [action_balancedWalsh]
  simp [walsh, Fin.sum_univ_succ]
  ring

lemma inverseWalsh_balanced_one (p : AlgebraicComplex) (sigma : Fin 3 → AlgebraicComplex) :
    action walsh (balancedWalsh p sigma) (fun _ => true) =
      2 * (p + ∑ j, sigma j) := by
  rw [action_balancedWalsh]
  simp [walsh, centralWord, flipPair, flipAll, Fin.prod_univ_succ, Fin.sum_univ_succ]
  ring

lemma inverseWalsh_balanced_central (p : AlgebraicComplex) (sigma : Fin 3 → AlgebraicComplex)
    (j : Fin 3) :
    action walsh (balancedWalsh p sigma) (centralWord j (fun _ => false)) =
      2 * (p + 2 * sigma j - ∑ i, sigma i) := by
  rw [action_balancedWalsh]
  fin_cases j <;>
    simp [walsh, centralWord, flipPair, flipAll, Fin.prod_univ_succ, Fin.sum_univ_succ] <;>
    ring

lemma inverseWalsh_balanced_central_complement
    (p : AlgebraicComplex) (sigma : Fin 3 → AlgebraicComplex) (j : Fin 3) :
    action walsh (balancedWalsh p sigma) (flipAll (centralWord j (fun _ => false))) =
      2 * (p + 2 * sigma j - ∑ i, sigma i) := by
  rw [action_balancedWalsh]
  fin_cases j <;>
    simp [walsh, centralWord, flipPair, flipAll, Fin.prod_univ_succ, Fin.sum_univ_succ] <;>
    ring

/-- All eight odd native coefficients vanish, with no ARS assumption on the
three possibly complex central coefficients. -/
lemma inverseWalsh_balanced_even
    (p : AlgebraicComplex) (sigma : Fin 3 → AlgebraicComplex) :
    SupportedOnParity (action walsh (balancedWalsh p sigma)) 0 := by
  intro x hx
  by_contra hodd
  have hw : parity x = 1 := by
    have h := Nat.mod_lt (Paper2.weight x) (by decide : 0 < 2)
    unfold parity at *
    omega
  have hz : action walsh (balancedWalsh p sigma) x = 0 := by
    rw [action_balancedWalsh]
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
    all_goals simp only [parity, Paper2.weight, Fin.sum_univ_four,
      h0, h1, h2, h3, Bool.false_eq_true, if_false, if_true] at hw
    all_goals norm_num at hw
    all_goals simp [walsh, centralWord, flipPair, flipAll, Fin.prod_univ_succ,
      Fin.sum_univ_succ, h0, h1, h2, h3]
  exact hx hz

/-- Except for the zero endpoint sum, balanced inverse Walsh tables have the
precise even support and two nonzero endpoints needed by the proved Section 6
classification. -/
theorem inverseWalsh_balanced_eightVertex
    (p : AlgebraicComplex) (sigma : Fin 3 → AlgebraicComplex)
    (hsum : p + ∑ i, sigma i ≠ 0) :
    Paper2.HeightTwo.EvenSupport (action walsh (balancedWalsh p sigma)) ∧
      action walsh (balancedWalsh p sigma) (fun _ => false) ≠ 0 ∧
      action walsh (balancedWalsh p sigma) (fun _ => true) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact Nat.even_iff.mpr (inverseWalsh_balanced_even p sigma x hx)
  · rw [inverseWalsh_balanced_zero]
    exact mul_ne_zero (by norm_num) hsum
  · rw [inverseWalsh_balanced_one]
    exact mul_ne_zero (by norm_num) hsum

end
end Paper2.HeightOne.Cyclic
