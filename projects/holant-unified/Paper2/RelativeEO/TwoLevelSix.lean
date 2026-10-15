import Paper2.ReedMullerNormalization.Endpoint
import Paper2.RelativeEO.MatchingComplementSix
import Paper2.RelativeEO.ARSMatching

/-! A direct relative-EO exit for the six-port endpoint-repair output.
Closing one displayed opposite pair gives a literal quaternary.  Unless its
two complementary coefficient products agree, that output is nonmatching.
The exceptional endpoint ratio is real, so the original six-port output is
projectively ARS over the actual algebraic field. -/
namespace Paper2.RelativeEO
open Tractable ReedMullerNormalization

noncomputable def twoLevelQuad {K : Type*} [CommRing K] (A B c : K) : Signature K 4 :=
  Signature.contract Signature.disequality (sixOutput A B c)

theorem twoLevelQuad_formula {K : Type*} [CommRing K] (A B c : K)
    (x : Fin 4 → Bool) :
    twoLevelQuad A B c x =
      if x 1 = !(x 0) ∧ x 3 = !(x 2) then
        (if x 0 = x 2 then A*B + 3*c^2 else 4*c^2) else 0 := by
  rw [twoLevelQuad,Signature.contract_disequality]
  simp only [sixOutput_formula]
  have he : x = ![x 0,x 1,x 2,x 3] := by funext i; fin_cases i <;> rfl
  rw [he]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    norm_num [ReedMullerNormalization.Opposite,Antipodal] <;> ring

theorem twoLevelQuad_central {K : Type*} [CommRing K] (A B c : K) :
    Signature.CentralSupport (twoLevelQuad A B c) := by
  intro x hx
  have hpair : ¬ (x 1 = !(x 0) ∧ x 3 = !(x 2)) := by
    intro hp
    apply hx
    have hh : ∀ y : Fin 4 → Bool, y 1 = !(y 0) ∧ y 3 = !(y 2) → 2 * weight y = 4 := by
      decide +kernel
    exact hh x hp
  simp [twoLevelQuad_formula,hpair]

theorem twoLevelQuad_ne_zero {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (A B c : K) (hc : c ≠ 0) : twoLevelQuad A B c ≠ 0 := by
  intro hz
  have hh := congrFun hz (![false,true,true,false] : Fin 4 → Bool)
  have h4 : (4 : K) * c^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hc)
  apply h4
  simpa [twoLevelQuad_formula] using hh

/-- This proof checks all three literal four-port matchings, including the
case where the same-bit coefficient vanishes. -/
theorem twoLevelQuad_not_matching {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (A B c : K) (hc : c ≠ 0)
    (hdet : (A*B+3*c^2)^2 ≠ (4*c^2)^2) :
    ¬ WeightedMatching.IsProduct (twoLevelQuad A B c) := by
  intro hm
  have hs : (4 : K) * c^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hc)
  rcases MatchingComplement.quaternary_matching_three_cases hm with h | h | h
  · apply hdet
    have hh := h.2.2.2.2.2.2
    simpa [MatchingComplement.sixWord,twoLevelQuad_formula,pow_two] using hh
  · have hh := h.2.2.1
    simp [MatchingComplement.sixWord,twoLevelQuad_formula] at hh
  · have hh := h.2.2.1
    simp [MatchingComplement.sixWord,twoLevelQuad_formula] at hh

theorem twoLevelQuad_exceptional_ratio {K : Type*} [CommRing K] [IsDomain K]
    (A B c : K) (hneq : A*B ≠ c^2)
    (hdet : (A*B+3*c^2)^2 = (4*c^2)^2) : A*B = -7*c^2 := by
  have hprod : (A*B-c^2)*(A*B+7*c^2) = 0 := by
    linear_combination hdet
  rcases mul_eq_zero.mp hprod with h | h
  · exact False.elim (hneq (sub_eq_zero.mp h))
  · linear_combination h

private theorem opposite_compl (x : Fin 6 → Bool) :
    Opposite (fun i => !(x i)) ↔ Opposite x := by
  revert x
  decide +kernel

private theorem antipodal_compl (x : Fin 6 → Bool) :
    Antipodal (fun i => !(x i)) ↔ Antipodal x := by
  revert x
  decide +kernel

/-- At the only exceptional ratio, normalizing by the actual nonzero c²
leaves the real complementary coefficients -6 and 2. -/
theorem sixOutput_exceptional_projectiveARS (A B c : AlgebraicComplex)
    (hc : c ≠ 0) (hab : A*B = -7*c^2) : ProjectiveARS (sixOutput A B c) := by
  refine ⟨c^2,pow_ne_zero _ hc,?_⟩
  intro x
  simp only [sixOutput_formula,opposite_compl,antipodal_compl,hab]
  by_cases ho : ReedMullerNormalization.Opposite x
  · simp only [ho,ite_true]
    by_cases ha : Antipodal x
    · simp only [ha,ite_true]
      have he : -7*c^2+c^2 = -6*c^2 := by ring
      rw [he]
      change ((c : ℂ)^2)⁻¹ * (-6*(c : ℂ)^2) = star (((c : ℂ)^2)⁻¹ * (-6*(c : ℂ)^2))
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
      have hn : ((c : ℂ)^2)⁻¹ * (-6*(c : ℂ)^2) = -6 := by field_simp [hcC]
      rw [hn]
      simp
    · simp only [ha,ite_false]
      change ((c : ℂ)^2)⁻¹ * (2*(c : ℂ)^2) = star (((c : ℂ)^2)⁻¹ * (2*(c : ℂ)^2))
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
      have hn : ((c : ℂ)^2)⁻¹ * (2*(c : ℂ)^2) = 2 := by field_simp [hcC]
      rw [hn]
      simp
  · simp only [ho,ite_false]
    simp

end Paper2.RelativeEO
