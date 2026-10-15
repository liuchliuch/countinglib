import Paper2.Tractable.Affine
import Paper2.Tractable.Product
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

/-! Determinants of full-support binary members of the actual affine/product
normal forms.  These are necessary conditions proved from their definitions;
no class-recognition or relative-EO conclusion is assumed. -/
namespace Paper2.RelativeEO
open Paper2.Tractable
open scoped BigOperators

private theorem imaginaryUnit_pow_mod_four (n : ℕ) :
    imaginaryUnit ^ (n % 4) = imaginaryUnit ^ n := by
  symm
  calc
    imaginaryUnit ^ n = imaginaryUnit ^ (n % 4 + 4 * (n / 4)) :=
      congrArg (fun k => imaginaryUnit ^ k) (Nat.mod_add_div n 4).symm
    _ = imaginaryUnit ^ (n % 4) := by
      rw [pow_add, pow_mul, imaginaryUnit_pow_four, one_pow, mul_one]

theorem fourthRootPhase_add (a b : ZMod 4) :
    fourthRootPhase (a + b) = fourthRootPhase a * fourthRootPhase b := by
  simp only [fourthRootPhase, ZMod.val_add, imaginaryUnit_pow_mod_four, pow_add]

/-- The even mixed coefficient is precisely the possible determinant sign. -/
theorem affine_binary_full_support {g : Signature AlgebraicComplex 2}
    (hg : Affine g) (hnz : ∀ x, g x ≠ 0) :
    g ![false, false] * g ![true, true] = g ![false, true] * g ![true, false] ∨
    g ![false, false] * g ![true, true] = -(g ![false, true] * g ![true, false]) := by
  rcases hg with rfl | ⟨s, hs, S, Q, rfl⟩
  · exact False.elim (hnz (fun _ => false) rfl)
  have hS : ∀ x, S.Holds x := by
    intro x
    by_contra h
    exact hnz x (by simp [affineFormula, h])
  have hp : fourthRootPhase (Q.eval ![false, false]) * fourthRootPhase (Q.eval ![true, true]) =
      (fourthRootPhase (Q.eval ![false, true]) * fourthRootPhase (Q.eval ![true, false])) *
        fourthRootPhase (Q.mixed 0 1) := by
    rw [← fourthRootPhase_add, ← fourthRootPhase_add, ← fourthRootPhase_add]
    congr 1
    simp [QuadraticPhase.eval, Fin.sum_univ_two, bitValue]
    ring
  simp only [affineFormula, hS, ↓reduceIte]
  rcases Q.even_mixed 0 1 (by decide) with h | h
  · left
    rw [h, fourthRootPhase_zero, mul_one] at hp
    linear_combination s ^ 2 * hp
  · right
    have phaseTwo : fourthRootPhase (2 : ZMod 4) = -1 := by
      change imaginaryUnit ^ 2 = -1
      exact imaginaryUnit_sq
    rw [h, phaseTwo] at hp
    linear_combination s ^ 2 * hp

private theorem productFactor_binary_full_support (p : ProductFactor 2)
    (hnz : ∀ x, p.eval x ≠ 0) :
    p.eval ![false, false] * p.eval ![true, true] =
      p.eval ![false, true] * p.eval ![true, false] := by
  have h00 := hnz ![false, false]
  have h01 := hnz ![false, true]
  cases p with
  | unary j u hu => fin_cases j <;> simp [ProductFactor.eval, mul_comm]
  | equality j k =>
    fin_cases j <;> fin_cases k <;>
      simp_all [ProductFactor.eval, Signature.equality]
  | disequality j k =>
    fin_cases j <;> fin_cases k <;> simp [ProductFactor.eval, Signature.disequality] at h00

/-- Repeated-variable factors are retained; full support rules out their
nontrivial equality/disequality constraints and leaves genuine unary products. -/
theorem product_binary_full_support {g : Signature AlgebraicComplex 2}
    (hg : Product g) (hnz : ∀ x, g x ≠ 0) :
    g ![false, false] * g ![true, true] = g ![false, true] * g ![true, false] := by
  rcases hg with rfl | ⟨s, hs, fs, rfl⟩
  · exact False.elim (hnz (fun _ => false) rfl)
  have hfactor : ∀ p ∈ fs, ∀ x, p.eval x ≠ 0 := by
    intro p hp x hx
    have hz : (fs.map (fun h => h.eval x)).prod = 0 :=
      List.prod_eq_zero_iff.mpr (List.mem_map.mpr ⟨p, hp, hx⟩)
    exact hnz x (by simp [productFormula, hz])
  have hprod :
      (fs.map (fun p => p.eval ![false, false])).prod * (fs.map (fun p => p.eval ![true, true])).prod =
      (fs.map (fun p => p.eval ![false, true])).prod * (fs.map (fun p => p.eval ![true, false])).prod := by
    clear hnz hs s
    induction fs with
    | nil => simp
    | cons p ps ih =>
      have hp := productFactor_binary_full_support p (hfactor p (by simp))
      have hi := ih (fun q hq => hfactor q (by simp [hq]))
      simp only [List.map_cons, List.prod_cons]
      calc
        _ = (p.eval ![false, false] * p.eval ![true, true]) *
            ((ps.map (fun q => q.eval ![false, false])).prod *
             (ps.map (fun q => q.eval ![true, true])).prod) := by ring
        _ = _ := by rw [hp, hi]; ring
  simp only [productFormula]
  linear_combination s ^ 2 * hprod

end Paper2.RelativeEO

