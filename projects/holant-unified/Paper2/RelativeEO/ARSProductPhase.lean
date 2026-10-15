import Paper2.RelativeEO.ARSFactorAccess

/-! The literal B_ARS matching definition implies the source's algebraic
projective ARS predicate, with its displayed overall scalar as normalizer. -/
namespace Paper2.RelativeEO
open Tractable
open scoped BigOperators

theorem IsARSProduct.projectiveARS {n : ℕ} {f : Signature AlgebraicComplex n}
    (h : IsARSProduct f) : ProjectiveARS f := by
  obtain ⟨P,a,c,hc,_,hf⟩ := h
  let φ : AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom
  have hvalues (x : Fin n → Bool) :
      (f x : ℂ) = (c : ℂ) * ∏ j,
        WeightedMatching.binary (a j : ℂ) (star (a j : ℂ))
          (x (P.ports (j,false))) (x (P.ports (j,true))) := by
    rw [hf]
    change φ (c * ∏ j, WeightedMatching.binary (a j) (conjugateAlgebraic (a j))
      (x (P.ports (j,false))) (x (P.ports (j,true)))) = _
    rw [map_mul,map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    cases x (P.ports (j,false)) <;> cases x (P.ports (j,true)) <;> rfl
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  refine ⟨c,hc,fun x => ?_⟩
  rw [hvalues,hvalues]
  simp only [← mul_assoc,inv_mul_cancel₀ hcC,one_mul,star_prod]
  symm
  apply Finset.prod_congr rfl
  intro j _
  cases x (P.ports (j,false)) <;> cases x (P.ports (j,true)) <;>
    simp [WeightedMatching.binary]

end Paper2.RelativeEO
