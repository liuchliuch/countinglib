import Paper2.Paper1ProvedOddUnaryNRSupportSlices
import Paper2.Paper1ProvedOddUnaryNRReconstruct

/-! The full sheared-class slice theorem, including its exact contrapositive.
The support partition, coefficient inheritance, and ordered tensor
reconstruction are all proved separately and combined here. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- At arity at least four, literal zero and one slices in the sheared
class force the complete signature into that same tensor class. -/
theorem closed_of_slices {n : ℕ} (f : Holant.Signature K (n+4))
    (hs : ∀ i v,Closed (slice f i v)) : Closed f := by
  by_cases zero : f=0
  · exact Or.inl zero
  · exact closed_of_partition_support (partition_support_of_closed_slices f hs zero)
      (closed_slices_inheritance (n:=n+2) f hs)

/-- Every failure of the high-arity tensor criterion has an actual literal
coordinate slice that still fails the criterion. -/
theorem exists_not_closed_slice {n : ℕ} (f : Holant.Signature K (n+4))
    (outside : ¬Closed f) : ∃ i v,¬Closed (slice f i v) := by
  classical
  by_contra none
  apply outside
  apply closed_of_slices
  intro i v
  by_contra failure
  exact none ⟨i,v,failure⟩

/-- Bound-form version, for callers retaining the original successor arity. -/
theorem closed_of_slices_of_four_le {n : ℕ} (f : Holant.Signature K (n+1))
    (large : 4≤n+1) (hs : ∀ i v,Closed (slice f i v)) : Closed f := by
  obtain ⟨k,hk⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
  subst n
  exact closed_of_slices f hs

theorem exists_not_closed_slice_of_four_le {n : ℕ} (f : Holant.Signature K (n+1))
    (large : 4≤n+1) (outside : ¬Closed f) : ∃ i v,¬Closed (slice f i v) := by
  obtain ⟨k,hk⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
  subst n
  exact exists_not_closed_slice f outside

end
end Paper2.Paper1Proved.OddUnary.NR

