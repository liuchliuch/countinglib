import Paper2.HeightThree.CardValues

/-! The literal graph contraction equals the Appendix A two-copy array. -/
namespace Paper2.HeightThree
open Certificates.Q6
open scoped BigOperators

variable {K : Type} [CommRing K]

lemma cardNetwork_endpoints_central (a b : K) (q : Fin 20 → K)
    (s : CardSpec) (hs : RawValidCardSpec s) (x : Fin 4 → Bool) :
    (cardNetwork s hs (coordinateMountain a b q)).denote x =
    (if (x 0).toNat + (x 1).toNat = 0 ∧ (x 2).toNat + (x 3).toNat = 2 then a*b else 0) +
    (if (x 0).toNat + (x 1).toNat = 2 ∧ (x 2).toNat + (x 3).toNat = 0 then a*b else 0) +
    ∑ T ∈ (internalLeft s).powerset,
      coefficient q (mask (sourceSetsAt s x T).1) * coefficient q (mask (sourceSetsAt s x T).2) := by
  rw [cardNetwork_subset_sum]
  trans ∑ T ∈ (internalLeft s).powerset,
    ((if T = ∅ then (if (x 0).toNat + (x 1).toNat = 0 ∧ (x 2).toNat + (x 3).toNat = 2
      then a*b else 0) else 0) +
    (if T = internalLeft s then (if (x 0).toNat + (x 1).toNat = 2 ∧ (x 2).toNat + (x 3).toNat = 0
      then a*b else 0) else 0) +
    coefficient q (mask (sourceSetsAt s x T).1) * coefficient q (mask (sourceSetsAt s x T).2))
  · apply Finset.sum_congr rfl
    intro T hT
    exact card_term a b q s hs x T (Finset.mem_powerset.mp hT)
  · rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
    simp

lemma card_central_filter (q : Fin 20 → K) (s : CardSpec) (hs : RawValidCardSpec s) (e : Fin 6) :
    (∑ T ∈ (internalLeft s).powerset,
      coefficient q (mask (sourceSetsAt s (eoWords e) T).1) *
        coefficient q (mask (sourceSetsAt s (eoWords e) T).2)) =
    ∑ T ∈ internalChoices s e,
      coefficient q (sourceMasks s e T).1 * coefficient q (sourceMasks s e T).2 := by
  unfold internalChoices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  have hc := (sourceSetsAt_cards s hs (eoWords e) T (Finset.mem_powerset.mp hT)).1
  have hw := twoBool_weight_le (eoWords e 0) (eoWords e 1)
  by_cases ht : T.card = 3-((eoWords e 0).toNat + (eoWords e 1).toNat)
  · simp only [ht,ite_true]
    rfl
  · rw [if_neg ht]
    have hz : (sourceSetsAt s (eoWords e) T).1.card ≠ 3 := by rw [hc]; omega
    rw [coefficient_mask_zero q _ hz,zero_mul]

/-- Both copies of the original M, all four native-X edges, and all summands
are represented by the network on the left. -/
theorem cardNetwork_array (a b : K) (q : Fin 20 → K) (s : CardSpec)
    (hs : RawValidCardSpec s) (e : Fin 6) :
    (cardNetwork s hs (coordinateMountain a b q)).denote (eoWords e) =
      twoCopyArray q (a*b) s e := by
  rw [cardNetwork_endpoints_central,card_central_filter q s hs e]
  unfold twoCopyArray
  congr 1
  fin_cases e <;> simp [eoWords]

end Paper2.HeightThree
