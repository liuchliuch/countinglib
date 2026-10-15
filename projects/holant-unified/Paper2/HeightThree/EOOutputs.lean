import Paper2.HeightThree.CardArray
import Paper2.Tractable.Criteria

namespace Paper2.HeightThree
open Certificates.Q6
open scoped BigOperators

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma weight_four (x : Fin 4 → Bool) :
    weight x = ((x 0).toNat + (x 1).toNat) + ((x 2).toNat + (x 3).toNat) := by
  revert x
  decide +kernel

variable {K : Type} [CommRing K]

lemma loopSignature_zero_off_two (a b : K) (q : Fin 20 → K)
    (i : Fin 15) (x : Fin 4 → Bool) (hx : weight x ≠ 2) :
    loopSignature (coordinateMountain a b q) i x = 0 := by
  unfold loopSignature
  apply Finset.sum_eq_zero
  intro t _
  have hcard : (occupied (loopWord i x t)).card ≠ 3 := by
    rw [occupied_card_weight,loopWord_weight]
    omega
  simp only [coordinateMountain,loopWord_not_constant,ite_false,zero_add,
    coefficient_mask_zero q _ hcard]

lemma cardNetwork_zero_off_two (a b : K) (q : Fin 20 → K)
    (s : CardSpec) (hs : RawValidCardSpec s) (x : Fin 4 → Bool) (hx : weight x ≠ 2) :
    (cardNetwork s hs (coordinateMountain a b q)).denote x = 0 := by
  have hw := weight_four x
  have h0 : ¬ ((x 0).toNat + (x 1).toNat = 0 ∧ (x 2).toNat + (x 3).toNat = 2) := by omega
  have h1 : ¬ ((x 0).toNat + (x 1).toNat = 2 ∧ (x 2).toNat + (x 3).toNat = 0) := by omega
  rw [cardNetwork_endpoints_central,if_neg h0,if_neg h1,zero_add,zero_add]
  apply Finset.sum_eq_zero
  intro T hT
  have hc := sourceSetsAt_cards s hs x T (Finset.mem_powerset.mp hT)
  have ht := internal_subset_card_le s hs T (Finset.mem_powerset.mp hT)
  by_cases hl : (sourceSetsAt s x T).1.card = 3
  · have hr : (sourceSetsAt s x T).2.card ≠ 3 := by omega
    rw [coefficient_mask_zero q _ hr,mul_zero]
  · rw [coefficient_mask_zero q _ hl,zero_mul]

lemma isEO_of_quaternary_support (f : Signature Tractable.AlgebraicComplex 4)
    (h : ∀ x, weight x ≠ 2 → f x = 0) : Tractable.IsEO ⟨4,f⟩ := by
  refine ⟨⟨2,rfl⟩,?_⟩
  intro x hx
  apply h x
  change 2 * weight x ≠ 4 at hx
  omega

theorem loopSignature_isEO (a b : Tractable.AlgebraicComplex) (q : Fin 20 → Tractable.AlgebraicComplex)
    (i : Fin 15) : Tractable.IsEO ⟨4,loopSignature (coordinateMountain a b q) i⟩ :=
  isEO_of_quaternary_support _ (loopSignature_zero_off_two a b q i)

theorem cardNetwork_isEO (a b : Tractable.AlgebraicComplex) (q : Fin 20 → Tractable.AlgebraicComplex)
    (s : CardSpec) (hs : RawValidCardSpec s) :
    Tractable.IsEO ⟨4,(cardNetwork s hs (coordinateMountain a b q)).denote⟩ :=
  isEO_of_quaternary_support _ (cardNetwork_zero_off_two a b q s hs)

end Paper2.HeightThree
