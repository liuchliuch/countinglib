import Paper2.RelativeEO.GramValues
import Paper2.RelativeEO.GramFactor
import Paper2.RelativeEO.GramCauchy
import Paper2.RelativeEO.MatchingComplementSix

/-! A direct two-copy replacement for the projective-ARS local descent.
A prime EO–ARS signature of arity at least four has a nonmatching quaternary
mating. The proof combines the finite central-weight variance identity with
positive Gram equality and a literal tensor-factor identity. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable EndpointSelfLoop
open scoped BigOperators
noncomputable section
variable {n : ℕ}
local instance (i j : Fin n) : DecidableEq (Remaining i j) := Classical.decEq _

private theorem six_quad (k : Fin 6) : MatchingComplement.sixWord k =
    ![quadWord false false true true,quadWord false true false true,
      quadWord false true true false,quadWord true false false true,
      quadWord true false true false,quadWord true true false false] k := by
  revert k
  decide +kernel


/-- At any unequal-mass pair, a matching Gram output would expose an actual
binary tensor factor, contradicting primality. -/
theorem gramTable_not_matching (i j : Fin n) (hij : i ≠ j) (hn : 4 ≤ n)
    (f : Signature AlgebraicComplex n) (hp : TensorPrime f) (hs : ARS f)
    (hneq : sliceMass i j hij f false false ≠ sliceMass i j hij f false true) :
    ¬ WeightedMatching.IsProduct (gramTable i j hij f) := by
  intro hm
  let H := gramTable i j hij f
  let A := sliceMass i j hij f false false
  let B := sliceMass i j hij f false true
  let C := gramCross i j hij f
  have hA : 0 ≤ A := sliceMass_nonneg i j hij f false false
  have hB : 0 ≤ B := sliceMass_nonneg i j hij f false true
  have hMassA : sliceMass i j hij f true true = A := sliceMass_complement i j hij f hs false false
  have hMassB : sliceMass i j hij f true false = B := sliceMass_complement i j hij f hs false true
  have h0 : (H (MatchingComplement.sixWord 0) : ℂ) = (A : ℂ) := by
    rw [six_quad]
    exact gramTable_norm i j hij f hs false false
  have h1 : (H (MatchingComplement.sixWord 1) : ℂ) = C := by
    rw [six_quad]
    exact gramTable_cross i j hij f hs
  have h2 : (H (MatchingComplement.sixWord 2) : ℂ) = (B : ℂ) := by
    rw [six_quad]
    exact gramTable_norm i j hij f hs false true
  have h3 : (H (MatchingComplement.sixWord 3) : ℂ) = (B : ℂ) := by
    rw [six_quad]
    have hh := gramTable_norm i j hij f hs true false
    rw [hMassB] at hh
    exact hh
  have h4 : (H (MatchingComplement.sixWord 4) : ℂ) = star C := by
    rw [six_quad]
    exact gramTable_cross_star i j hij f hs
  have h5 : (H (MatchingComplement.sixWord 5) : ℂ) = (A : ℂ) := by
    rw [six_quad]
    have hh := gramTable_norm i j hij f hs true true
    rw [hMassA] at hh
    exact hh
  have coe_zero {z : AlgebraicComplex} (hz : z = 0) : (z : ℂ) = 0 := congrArg Subtype.val hz
  have hzC (hb0 : B = 0) : C = 0 := by
    have hu := sliceMass_eq_zero i j hij f false true hb0
    simp only [C,gramCross,hu,ZeroMemClass.coe_zero,zero_mul,Finset.sum_const_zero]
  rcases MatchingComplement.quaternary_matching_three_cases hm with h | h | h
  · obtain ⟨hz,_,hcn,_,hbn,_,he⟩ := h
    have ha0 : A = 0 := by
      have hh := coe_zero hz
      rw [h0] at hh
      exact_mod_cast hh
    have hb0 : B ≠ 0 := by
      intro hz
      apply hbn
      apply Subtype.ext
      rw [h2,hz]
      rfl
    have hbpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hb0)
    have hcs : Complex.normSq C = B^2 := by
      have hh := congrArg Subtype.val he
      change (H (MatchingComplement.sixWord 1) : ℂ) * (H (MatchingComplement.sixWord 4) : ℂ) =
        (H (MatchingComplement.sixWord 2) : ℂ) * (H (MatchingComplement.sixWord 3) : ℂ) at hh
      rw [h1,h4,h2,h3,Complex.star_def,Complex.mul_conj] at hh
      have hhR : Complex.normSq C = B*B := by exact_mod_cast hh
      nlinarith only [hhR]
    obtain ⟨r,_,hr⟩ := algebraic_proportional_of_gram_equality
      (pairSlice i j hij f false true) (pairSlice i j hij f true false) B hbpos rfl
      (by exact sliceMass_complement i j hij f hs false true) hcs
    apply gram_slices_not_prime i j hij hn f r
      (sliceMass_eq_zero i j hij f false false ha0)
      (sliceMass_eq_zero i j hij f true true (hMassA.trans ha0)) hr hp
  · obtain ⟨_,_,_,_,_,_,he⟩ := h
    have hh := congrArg Subtype.val he
    change (H (MatchingComplement.sixWord 0) : ℂ) * (H (MatchingComplement.sixWord 5) : ℂ) =
      (H (MatchingComplement.sixWord 2) : ℂ) * (H (MatchingComplement.sixWord 3) : ℂ) at hh
    rw [h0,h5,h2,h3] at hh
    have hhR : A*A = B*B := by exact_mod_cast hh
    exact hneq (by nlinarith only [hA,hB,hhR])
  · obtain ⟨hz,_,_,_,hcn,_,_⟩ := h
    have hb0 : B = 0 := by
      have hh := coe_zero hz
      rw [h2] at hh
      exact_mod_cast hh
    apply hcn
    apply Subtype.ext
    rw [h1,hzC hb0]
    rfl


/-- Every prime exact EO–ARS input of positive nonbinary arity has an actual
nonmatching quaternary two-copy output; no generic arity-six base is assumed. -/
theorem prime_ARS_nonmatching_mating (f : Signature AlgebraicComplex n)
    (hn : 4 ≤ n) (hp : TensorPrime f) (he : Signature.CentralSupport f) (hs : ARS f) :
    ∃ (i j : Fin n) (hij : i ≠ j),
      gramTable i j hij f ≠ 0 ∧ Signature.CentralSupport (gramTable i j hij f) ∧
      ¬ WeightedMatching.IsProduct (gramTable i j hij f) := by
  have hnz : (fun x => (f x : ℂ)) ≠ 0 := by
    intro hz
    apply hp.1
    funext x
    exact Subtype.ext (congrFun hz x)
  have heC : Signature.CentralSupport (fun x => (f x : ℂ)) := by
    intro x hx
    change (f x : ℂ) = 0
    rw [he x hx]
    rfl
  obtain ⟨i,j,hij,hneq⟩ := exists_unequal_pair_mass (fun x => (f x : ℂ)) (by omega) hnz heC
  rw [pairMass_slice i j hij,pairMass_slice i j hij] at hneq
  exact ⟨i,j,hij,gramTable_ne_zero i j hij f hp.1 hs,gramTable_central i j hij f he,
    gramTable_not_matching i j hij hn f hp hs hneq⟩

end
end Paper2.RelativeEO
