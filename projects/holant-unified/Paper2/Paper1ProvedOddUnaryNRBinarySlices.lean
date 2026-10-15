import Paper2.Paper1ProvedOddUnaryNRReconstruct
import Paper2.Paper1ProvedOddUnaryNRSlices

/-! At arity two every hereditary support is either a single allowed block
or two independent allowed blocks. Exact NR coefficient inheritance therefore
already reconstructs the full binary tensor. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [CharZero K]

private theorem binary_single_zero : (single (0 : Fin 2))=![true,false] := by
  funext i
  fin_cases i <;> simp [single,word]

private theorem binary_single_one : (single (1 : Fin 2))=![false,true] := by
  funext i
  fin_cases i <;> simp [single,word]

theorem partition_support_binary_of_inheritance (f : Holant.Signature K 2)
    (inherited : Inheritance f) (nonzero : f≠0) : PartitionSupport f := by
  classical
  have origin : f ![false,false]≠0 := by
    obtain ⟨x,live⟩ : ∃ x,f x≠0 := by
      by_contra none
      apply nonzero
      funext x
      by_contra live
      exact none ⟨x,live⟩
    have h := inheritance_origin_live inherited x live
    have wordeq : (![false,false] : Fin 2 → Bool)=(fun _ => false) := by
      funext i
      fin_cases i <;> rfl
    simpa only [wordeq] using h
  have lower (live : f ![true,true]≠0) (i : Fin 2) : f (single i)≠0 := by
    apply inheritance_support_downward inherited ![true,true] (single i) live
    intro j _
    fin_cases j <;> rfl
  let allowed : Fin 2 → Prop := fun i => f (single i)≠0
  let label : Fin 2 → Fin 2 := fun i => if f ![true,true]≠0 then i else 0
  refine ⟨2,allowed,label,?_⟩
  intro x
  have wordeq : x=![x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [wordeq]
  cases x 0 <;> cases x 1
  · simp [Matches,Fin.forall_fin_two,origin]
  · simp [Matches,Fin.forall_fin_two,allowed,binary_single_one]
  · simp [Matches,Fin.forall_fin_two,allowed,binary_single_zero]
  · by_cases live : f ![true,true]≠0
    · have l0 := lower live 0
      have l1 := lower live 1
      simp [Matches,Fin.forall_fin_two,allowed,label,live,l0,l1]
    · simp [Matches,Fin.forall_fin_two,label,live]

/-- Coefficient inheritance is sufficient at arity two; its support has no
room for a higher-order obstruction. -/
theorem closed_binary_of_inheritance (f : Holant.Signature K 2)
    (inherited : Inheritance f) : Closed f := by
  by_cases zero : f=0
  · exact Or.inl zero
  · exact closed_of_partition_support
      (partition_support_binary_of_inheritance f inherited zero) inherited

theorem closed_binary_of_slices (f : Holant.Signature K 2)
    (slices : ∀ i v,Closed (slice f i v)) : Closed f :=
  closed_binary_of_inheritance f (closed_slices_inheritance f slices)

end
end Paper2.Paper1Proved.OddUnary.NR

