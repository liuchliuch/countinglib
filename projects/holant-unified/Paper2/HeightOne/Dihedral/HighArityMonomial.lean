import Holant.Dihedral.TwoCardLocalization.DistinctProducts
import Holant.Dihedral.TwoCardLocalization.MonomialUniqueness
import Holant.Marked.Monomial

/-! Pure matching surgery on nonsingular monomial matrices. This ambient
matrix group records analytic factorization only; it supplies no additional
physical phases. Every localization instruction uses its specified kernel. -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Holant Holant.Marked Holant.Certificates
open Holant.Certificates.MatchingContractionClosure
set_option backward.isDefEq.respectTransparency false

def monomialGroup : Set (Matrix Bool Bool Scalar) := {A | IsMonomial A}

theorem monomial_matrix_group : ProjectiveMatrixGroup monomialGroup := by
  refine ⟨?_,?_,?_,?_⟩
  · have he : (1 : Matrix Bool Bool Scalar) = (Signature.equality : Mat) := by
      funext a b
      simp [Matrix.one_apply,Signature.equality]
    rw [he]
    exact equality_isMonomial
  · intro A hA B hB
    exact hA.mul hB
  · intro A hA
    obtain ⟨p,w,hw,rfl⟩ := hA
    let V : Mat := monomial p (fun a => (w (a ^^ p))⁻¹)
    have hV : V ∈ monomialGroup := ⟨p,_,fun a => inv_ne_zero (hw _),rfl⟩
    refine ⟨V,hV,?_,?_⟩
    · change Kernel.mul (monomial p w) V = Signature.equality
      funext a b
      cases p <;> cases a <;> cases b <;>
        simp [V,monomial,Kernel.mul_apply,Signature.equality,hw]
    · change Kernel.mul V (monomial p w) = Signature.equality
      funext a b
      cases p <;> cases a <;> cases b <;>
        simp [V,monomial,Kernel.mul_apply,Signature.equality,hw]
  · intro A hA c hc
    exact hA.scale hc

theorem monomial_X : (X : Matrix Bool Bool Scalar) ∈ monomialGroup :=
  disequality_isMonomial

theorem monomial_reversal : ReversalStable monomialGroup := by
  intro A hA
  exact (disequality_isMonomial.mul hA.transpose).mul disequality_isMonomial

theorem safe_monomial_iff (A : Matrix Bool Bool Scalar) :
    SafeBinary monomialGroup A ↔ IsMonomial A := by
  constructor
  · intro h
    have hh := Holant.Marked.IsMonomial.mul h disequality_isMonomial
    change IsMonomial (Kernel.mul (Kernel.mul A Signature.disequality) Signature.disequality) at hh
    rw [Kernel.mul_assoc,Kernel.disequality_mul_disequality,Kernel.mul_equality] at hh
    exact hh
  · intro h
    exact h.mul disequality_isMonomial

/-- Exact simultaneous localization with one supplied actual kernel. The
ambient analytic group is independent of the source's finite phase order. -/
theorem different_matching_program
    (C : Mat) (hC : IsMonomial C) (r : ℕ)
    (q₀ q₁ : Signature Scalar (2 * r + 4))
    (h : Holant.Dihedral.TwoCardLocalization.DifferentProducts monomialGroup _ q₀ q₁) :
    ∃ P : Holant.Dihedral.TwoCardLocalization.Program Unit (2 * r + 4) 4,
      P.length = r ∧
      Holant.Dihedral.TwoCardLocalization.DifferentProducts monomialGroup 4
        (P.residual (fun _ => C) q₀) (P.residual (fun _ => C) q₁) :=
  Holant.Dihedral.TwoCardLocalization.different_products_program monomialGroup
    monomial_matrix_group monomial_X monomial_reversal C
      ((safe_monomial_iff C).mpr hC) r q₀ q₁ h

end
end Paper2.HeightOne.Dihedral.HighArity
