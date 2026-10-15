import Paper2.HeightThree.CardWords

namespace Paper2.HeightThree
open Certificates.Q6
open scoped BigOperators
noncomputable section

variable {K : Type} [CommSemiring K]

/-- The complete direct graph value, with no discarded or individually
realizable summands. Its index set is exactly the four-port internal powerset. -/
lemma cardNetwork_subset_sum (s : CardSpec) (hs : RawValidCardSpec s)
    (M : Signature K 6) (x : Fin 4 → Bool) :
    (cardNetwork s hs M).denote x = ∑ T ∈ (internalLeft s).powerset,
      M (subsetWord (sourceSetsAt s x T).1) * M (subsetWord (sourceSetsAt s x T).2) := by
  rw [cardNetwork_denote]
  calc
    _ = ∑ z : LeftInterior s → Bool,
        M (subsetWord (sourceSetsAt s x (occupiedInternal s z)).1) *
        M (subsetWord (sourceSetsAt s x (occupiedInternal s z)).2) := by
      apply Finset.sum_congr rfl
      intro z _
      have hl := cardWord_left s hs x (occupiedInternal s z) (occupiedInternal_subset s z)
      have hr := cardWord_right s hs x (occupiedInternal s z)
      rw [internalAssignment_occupied] at hl hr
      rw [hl,hr]
    _ = _ := sum_internal_subsets s (fun T => M (subsetWord (sourceSetsAt s x T).1) * M (subsetWord (sourceSetsAt s x T).2))

end
end Paper2.HeightThree
