import Paper2.Paper1ProvedOddUnaryNRSupportSlices
import Paper2.Paper1ProvedOddUnaryNRReconstruct
import Paper2.Paper1ProvedOddUnaryNRSmallCoefficients

/-! A non-NR ternary whose literal coordinate slices are NR has an actual
ordinary loop exit in the canonical Gram chart. Three-port support paths
and a missing supported triple both force a unary outside the NR criterion. -/
namespace Paper2.Paper1Proved.OddUnary.NR.ThreeSlices
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [CharZero K]

def Distinct (i j k : Fin 3) : Prop := i≠j ∧ j≠k ∧ i≠k

/-- The scalar-free loop for Gram [[0,1],[1,-2]], leaving port k. -/
def loop (f : Holant.Signature K 3) (i j k : Fin 3) : Holant.Signature K 1 := fun x =>
  if x 0 then f (double i k)+f (double j k)-2*f (fun _ => true)
  else f (single i)+f (single j)-2*f (double i j)

theorem word_weight {n : ℕ} (s : Finset (Fin n)) : Holant.weight (word s)=s.card := by
  classical
  simp [Holant.weight,word]

theorem single_coefficient (f : Holant.Signature K 3) (inheritance : Inheritance f)
    (i : Fin 3) (live : f (single i)≠0) : 2*f (single i)=f (fun _ => false) := by
  have h := inheritance_normalizes inheritance (single i) live
  simpa only [single,word_weight,Finset.card_singleton,pow_one] using h

theorem double_coefficient (f : Holant.Signature K 3) (inheritance : Inheritance f)
    (i j : Fin 3) (ne : i≠j) (live : f (double i j)≠0) : 4*f (double i j)=f (fun _ => false) := by
  have h := inheritance_normalizes inheritance (double i j) live
  simp only [double,word_weight,Finset.card_pair ne] at h
  norm_num at h
  exact h

theorem pairwise_from_loops (f : Holant.Signature K 3)
    (hs : ∀ i v,Closed (slice f i v)) (nonzero : f≠0)
    (hl : ∀ i j k,Distinct i j k → Closed (loop f i j k)) : PairwiseSupport f := by
  classical
  have inherited := closed_slices_inheritance (n:=1) f hs
  obtain ⟨z,hz⟩ : ∃ z,f z≠0 := by
    by_contra none
    apply nonzero
    funext z
    by_contra live
    exact none ⟨z,live⟩
  have origin := inheritance_origin_live inherited z hz
  intro x
  constructor
  · intro live
    constructor
    · intro i hi
      exact inheritance_support_downward inherited x (single i) live (by
        intro j hj
        have ji : j=i := by simpa [single,word] using hj
        simpa [ji] using hi)
    · intro i j _ hi hj
      exact inheritance_support_downward inherited x (double i j) live (by
        intro k hk
        have member : k=i ∨ k=j := by simpa [double,word] using hk
        rcases member with rfl|rfl
        · exact hi
        · exact hj)
  · rintro ⟨singles,pairs⟩
    by_cases proper : ∃ i,x i=false
    · obtain ⟨i,hi⟩ := proper
      exact live_of_pairs_at_zero f hs origin x i hi singles pairs
    · have full : x=fun _ => true := by
        funext i
        cases hi : x i
        · exact False.elim (proper ⟨i,hi⟩)
        · rfl
      rw [full] at singles pairs ⊢
      by_contra zero
      have s0 := single_coefficient f inherited 0 (singles 0 rfl)
      have s1 := single_coefficient f inherited 1 (singles 1 rfl)
      have p01 := double_coefficient f inherited 0 1 (by decide) (pairs 0 1 (by decide) rfl rfl)
      have p02 := double_coefficient f inherited 0 2 (by decide) (pairs 0 2 (by decide) rfl rfl)
      have p12 := double_coefficient f inherited 1 2 (by decide) (pairs 1 2 (by decide) rfl rfl)
      rcases (closed_unary_iff _).mp (hl 0 1 2 ⟨by decide,by decide,by decide⟩) with hzero|hratio
      · simp only [loop,ite_true,zero,mul_zero,sub_zero] at hzero
        apply origin
        linear_combination 2*hzero-p02/2-p12/2
      · simp only [loop,Bool.false_eq_true,ite_false,ite_true,zero,mul_zero,sub_zero] at hratio
        apply origin
        linear_combination -(2*hratio)+s0+s1-p01- p02-p12

theorem conflict_from_loops (f : Holant.Signature K 3) (inherited : Inheritance f)
    (hl : ∀ i j k,Distinct i j k → Closed (loop f i j k))
    (i j k : Fin 3) (li : f (single i)≠0) (lj : f (single j)≠0) (lk : f (single k)≠0)
    (ij : i=j ∨ f (double i j)=0) (jk : j=k ∨ f (double j k)=0) : i=k ∨ f (double i k)=0 := by
  classical
  rcases ij with rfl|zij
  · exact jk
  rcases jk with rfl|zjk
  · exact Or.inr zij
  by_cases ik : i=k
  · exact Or.inl ik
  right
  by_contra lik
  have ij : i≠j := by
    intro equal
    subst j
    have h : double i i=single i := by simp [double,single]
    exact li (h ▸ zij)
  have jk : j≠k := by
    intro equal
    subst k
    have h : double j j=single j := by simp [double,single]
    exact lj (h ▸ zjk)
  have triple : f (fun _ => true)=0 := by
    by_contra live
    have pairlive := inheritance_support_downward inherited (fun _ => true) (double i j) live (by simp)
    exact pairlive zij
  have origin := inheritance_origin_live inherited (single i) li
  have si := single_coefficient f inherited i li
  have sj := single_coefficient f inherited j lj
  have pik := double_coefficient f inherited i k ik lik
  rcases (closed_unary_iff _).mp (hl i j k ⟨ij,jk,ik⟩) with zero|ratio
  · simp only [loop,ite_true,zjk,triple,mul_zero,add_zero,sub_zero] at zero
    apply origin
    linear_combination 4*zero-pik
  · simp only [loop,Bool.false_eq_true,ite_false,ite_true,zij,zjk,triple,mul_zero,add_zero,sub_zero] at ratio
    apply origin
    linear_combination 2*ratio-si-sj+pik

theorem closed_of_slices_and_loops (f : Holant.Signature K 3)
    (hs : ∀ i v,Closed (slice f i v))
    (hl : ∀ i j k,Distinct i j k → Closed (loop f i j k)) : Closed f := by
  by_cases zero : f=0
  · exact Or.inl zero
  have inherited := closed_slices_inheritance (n:=1) f hs
  have support := partition_of_pairwise_conflict f (pairwise_from_loops f hs zero hl)
    (conflict_from_loops f inherited hl)
  exact closed_of_partition_support support inherited

theorem exists_outside_loop (f : Holant.Signature K 3)
    (hs : ∀ i v,Closed (slice f i v)) (outside : ¬Closed f) :
    ∃ i j k,Distinct i j k ∧ ¬Closed (loop f i j k) := by
  classical
  by_contra none
  apply outside
  apply closed_of_slices_and_loops f hs
  intro i j k hd
  by_contra bad
  exact none ⟨i,j,k,hd,bad⟩

end
end Paper2.Paper1Proved.OddUnary.NR.ThreeSlices

