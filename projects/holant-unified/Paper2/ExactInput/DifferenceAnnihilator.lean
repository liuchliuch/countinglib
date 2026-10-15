import Paper2.ExactInput.LinearCombinationAnnihilator
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! A fixed-dimensional annihilator for every difference of conjugates, formed
inside K tensor K. The tensor algebra need not be a field. -/
namespace Paper2.ExactInput
open Paper2.Algebraic Polynomial
open scoped BigOperators TensorProduct

section
variable {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}

noncomputable def tensorDirection (F : FixedField K n) (i : Fin n) : K ⊗[ℚ] K :=
  (Algebra.TensorProduct.includeLeft : K →ₐ[ℚ] K ⊗[ℚ] K) (F.basis i) -
    (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] K ⊗[ℚ] K) (F.basis i)

noncomputable def differenceAnnihilator (F : FixedField K n) (v : Fin n → ℚ) : Polynomial ℚ :=
  combinationAnnihilator (F.basis.tensorProduct F.basis) (tensorDirection F) v

theorem differenceAnnihilator_monic (F : FixedField K n) (v : Fin n → ℚ) :
    (differenceAnnihilator F v).Monic := combinationAnnihilator_monic _ _ _

theorem differenceAnnihilator_height_bound (F : FixedField K n) :
    ∃ C : ℕ, ∀ (B : ℕ) (v : Fin n → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      ∀ j, rationalBitHeight ((differenceAnnihilator F v).coeff j) ≤ C * (B + 1) :=
  combinationAnnihilator_height_bound _ _

theorem differenceAnnihilator_embeddings (F : FixedField K n) (v : Fin n → ℚ)
    (σ τ : K →ₐ[ℚ] ℂ) :
    Polynomial.aeval (σ (F.decode v) - τ (F.decode v)) (differenceAnnihilator F v) = 0 := by
  let φ : (K ⊗[ℚ] K) →ₐ[ℚ] ℂ :=
    Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)
  have hval : φ (∑ i, v i • tensorDirection F i) = σ (F.decode v) - τ (F.decode v) := by
    rw [show F.decode v = ∑ i, v i • F.basis i from F.basis.equivFun_symm_apply v]
    simp [φ, tensorDirection, map_smul, smul_sub, Finset.sum_sub_distrib]
  rw [← hval, Polynomial.aeval_algHom_apply]
  rw [show Polynomial.aeval (∑ i, v i • tensorDirection F i) (differenceAnnihilator F v) = 0 from
    combinationAnnihilator_aeval _ _ _, map_zero]

/-- Every pair of actual minimal-polynomial roots, not only a preferred embedding,
has its difference annihilated by the same bounded polynomial. -/
theorem differenceAnnihilator_roots (F : FixedField K n) (v : Fin n → ℚ)
    {z w : ℂ} (hz : Polynomial.aeval z (minpoly ℚ (F.decode v)) = 0)
    (hw : Polynomial.aeval w (minpoly ℚ (F.decode v)) = 0) :
    Polynomial.aeval (z - w) (differenceAnnihilator F v) = 0 := by
  letI : Module.Finite ℚ K := Module.Finite.of_basis F.basis
  have hs : ∀ x : K, IsIntegral ℚ x ∧ ((minpoly ℚ x).map (algebraMap ℚ ℂ)).Splits :=
    fun x => ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩
  obtain ⟨σ, hσ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hs hz
  obtain ⟨τ, hτ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hs hw
  simpa only [hσ, hτ] using differenceAnnihilator_embeddings F v σ τ

end
end Paper2.ExactInput
