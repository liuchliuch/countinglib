import Paper2.HeightThree.CardSizes

/-! Endpoint/central expansion of the complete two-copy contraction.
Mixed endpoint-central terms vanish because four ports are wired. -/
namespace Paper2.HeightThree
open Certificates.Q6
open scoped BigOperators

lemma twoBool_weight_le (a b : Bool) : a.toNat + b.toNat ≤ 2 := by
  cases a <;> cases b <;> decide

variable {K : Type} [CommSemiring K]

lemma card_term (a b : K) (q : Fin 20 → K) (s : CardSpec) (hs : RawValidCardSpec s)
    (x : Fin 4 → Bool) (T : PortSet) (hT : T ⊆ internalLeft s) :
    coordinateMountain a b q (subsetWord (sourceSetsAt s x T).1) *
      coordinateMountain a b q (subsetWord (sourceSetsAt s x T).2) =
    (if T = ∅ then (if (x 0).toNat + (x 1).toNat = 0 ∧ (x 2).toNat + (x 3).toNat = 2
      then a*b else 0) else 0) +
    (if T = internalLeft s then (if (x 0).toNat + (x 1).toNat = 2 ∧ (x 2).toNat + (x 3).toNat = 0
      then a*b else 0) else 0) +
    coefficient q (mask (sourceSetsAt s x T).1) * coefficient q (mask (sourceSetsAt s x T).2) := by
  have hc := sourceSetsAt_cards s hs x T hT
  have hl := twoBool_weight_le (x 0) (x 1)
  have hr := twoBool_weight_le (x 2) (x 3)
  have ht := internal_subset_card_le s hs T hT
  have hil : internalLeft s ≠ ∅ := by
    intro h
    have hh := internalLeft_card s hs
    rw [h,Finset.card_empty] at hh
    omega
  by_cases h0 : T = ∅
  · subst T
    have hcl : coefficient q (mask (sourceSetsAt s x ∅).1) = 0 :=
      coefficient_mask_zero _ _ (by rw [hc.1]; simp only [Finset.card_empty,add_zero]; omega)
    have hcr : coefficient q (mask (sourceSetsAt s x ∅).2) = 0 :=
      coefficient_mask_zero _ _ (by rw [hc.2]; simp only [Finset.card_empty,Nat.sub_zero]; omega)
    rw [coordinateMountain_subset,coordinateMountain_subset,hcl,hcr,hc.1,hc.2]
    cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
      simp [h₀,h₁,h₂,h₃,hil,Ne.symm hil]
  by_cases h4 : T = internalLeft s
  · subst T
    have hcl : coefficient q (mask (sourceSetsAt s x (internalLeft s)).1) = 0 :=
      coefficient_mask_zero _ _ (by rw [hc.1,internalLeft_card s hs]; omega)
    have hcr : coefficient q (mask (sourceSetsAt s x (internalLeft s)).2) = 0 :=
      coefficient_mask_zero _ _ (by rw [hc.2,internalLeft_card s hs]; omega)
    rw [coordinateMountain_subset,coordinateMountain_subset,hcl,hcr,hc.1,hc.2,internalLeft_card s hs]
    cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
      simp [h₀,h₁,h₂,h₃,hil,mul_comm]
  · have ht0 : T.card ≠ 0 := fun h => h0 (Finset.card_eq_zero.mp h)
    have ht4 : T.card ≠ 4 := fun h => h4 ((internal_subset_card_eq_four s hs T hT).mp h)
    have hl0 : (sourceSetsAt s x T).1.card ≠ 0 := by rw [hc.1]; omega
    have hl6 : (sourceSetsAt s x T).1.card ≠ 6 := by rw [hc.1]; omega
    have hr0 : (sourceSetsAt s x T).2.card ≠ 0 := by rw [hc.2]; omega
    have hr6 : (sourceSetsAt s x T).2.card ≠ 6 := by rw [hc.2]; omega
    simp only [coordinateMountain_subset,hl0,hl6,hr0,hr6,h0,h4,ite_false,zero_add]

end Paper2.HeightThree
