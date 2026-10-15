import Paper2.Paper1ProvedOddUnaryNRSupport
import Paper2.Paper1ProvedOddUnaryWEscapeBinary

/-! The entire sheared family uses one of the two fixed source-K matching
orientations. Upper triangular coordinate changes preserve literal one-hot
support; a nonzero isotropic first column determines the common orientation. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.TractChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem weight_mono {n : ℕ} (x y : Fin n → Bool)
    (le : ∀ i,x i=true → y i=true) : Holant.weight x≤Holant.weight y := by
  unfold Holant.weight
  apply Finset.sum_le_sum
  intro i _
  cases hx : x i <;> cases hy : y i
  · simp
  · simp
  · have impossible := le i hx
    simp [hy] at impossible
  · simp

theorem upper_triangular_oneHot {K : Type*} [Field K] {n : ℕ}
    (M : Holant.Kernel K) (lower : M true false=0)
    {f : Holant.Signature K n} (hf : Holant.Signature.OneHot f) :
    Holant.Signature.OneHot (Holant.Signature.coordinateAction (fun _ => M) f) := by
  classical
  intro x high
  unfold Holant.Signature.coordinateAction
  apply Finset.sum_eq_zero
  intro y _
  by_cases yh : 1<Holant.weight y
  · rw [hf y yh,mul_zero]
  · obtain ⟨i,xi,yi⟩ : ∃ i,x i=true ∧ y i=false := by
      by_contra none
      have xy : Holant.weight x≤Holant.weight y := weight_mono x y (by
        intro i xi
        cases yi : y i
        · exact False.elim (none ⟨i,xi,yi⟩)
        · rfl)
      omega
    have zero : (∏ j,M (x j) (y j))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [xi,yi,lower])
    rw [zero,zero_mul]

theorem generator_oneHot {K : Type*} [Field K] {n : ℕ}
    {f : Holant.Signature K n} (hf : Generator n f) : Holant.Signature.OneHot f := by
  rcases hf with ⟨_,c,rfl⟩|⟨_,c,rfl⟩
  · intro x high
    simp [pin,Nat.ne_of_gt (by omega : 0<Holant.weight x)]
  · intro x high
    have zero : Holant.weight x≠0 := by omega
    have one : Holant.weight x≠1 := by omega
    simp [row,zero,one]

/-- Exact proportionality of the first columns makes the inverse fixed-K
coordinate matrix upper triangular. -/
theorem relative_lower_zero (A : Holant.Tractable.InvertibleKernel)
    (opposite : Bool) (c : AlgebraicComplex)
    (line : ∀ v,A.matrix v false=c*(TensorDecisionMatching.basis opposite).matrix v false) :
    ((TensorDecisionMatching.basis opposite).symm.comp A).matrix true false=0 := by
  let B := TensorDecisionMatching.basis opposite
  have inverse := congrFun (congrFun B.inverse_matrix true) false
  simp only [Holant.Kernel.mul_apply,Holant.Signature.equality] at inverse
  simp only [Bool.true_eq_false,ite_false] at inverse
  change Holant.Kernel.mul B.inverse A.matrix true false=0
  simp only [Holant.Kernel.mul_apply]
  rw [line false,line true]
  change B.inverse true false*(c*B.matrix false false)+
    B.inverse true true*(c*B.matrix true false)=0
  linear_combination c*inverse

theorem oneHot_action_matching (A : Holant.Tractable.InvertibleKernel)
    (opposite : Bool) (c : AlgebraicComplex)
    (line : ∀ v,A.matrix v false=c*(TensorDecisionMatching.basis opposite).matrix v false)
    {n : ℕ} (f : Holant.Signature AlgebraicComplex n) (hf : Holant.Signature.OneHot f) :
    matchingImage opposite n (A.action f) := by
  let B := TensorDecisionMatching.basis opposite
  let T := B.symm.comp A
  have ht : Holant.Signature.OneHot (T.action f) :=
    upper_triangular_oneHot T.matrix (relative_lower_zero A opposite c line) hf
  have transformed : B.symm.action (A.action f)=T.action f :=
    (InvertibleKernel.comp_action B.symm A f).symm
  have h := TensorDecisionMatching.forward_factor opposite n
    (B.symm.action (A.action f)) (by rw [transformed]; exact ht)
  simpa only [B,InvertibleKernel.action_symm_action] using h

theorem closed_action_matching (A : Holant.Tractable.InvertibleKernel)
    (opposite : Bool) (c : AlgebraicComplex)
    (line : ∀ v,A.matrix v false=c*(TensorDecisionMatching.basis opposite).matrix v false)
    {n : ℕ} {f : Holant.Signature AlgebraicComplex n} (hf : Closed f) :
    SourceTensorClosure (matchingImage opposite) (A.action f) := by
  rcases hf with rfl|tensor
  · left
    funext x
    simp [InvertibleKernel.action,Holant.Signature.coordinateAction]
  · right
    exact tensor.map_action A.matrix (fun m g hg =>
      oneHot_action_matching A opposite c line g (generator_oneHot hg))

theorem isotropic_first_nonzero (A : Holant.Tractable.InvertibleKernel)
    (iso : A.matrix false false^2+A.matrix true false^2=0) :
    A.matrix false false≠0 := by
  intro zero
  have other : A.matrix true false=0 := by
    have square : A.matrix true false^2=0 := by simpa [zero] using iso
    exact sq_eq_zero_iff.mp square
  apply Holant.Tractable.SymmetricBinaryPullback.determinant_ne_zero A
  simp [Holant.Tractable.SymmetricBinaryPullback.determinant,zero,other]

/-- The orientation is selected once, before the whole-family quantifier. -/
theorem closed_coordinates_matching (A : Holant.Tractable.InvertibleKernel)
    (iso : A.matrix false false^2+A.matrix true false^2=0)
    (F : Holant.SignatureFamily AlgebraicComplex)
    (rows : ∀ f∈F,Closed (A.symm.action f.2)) :
    ∃ opposite : Bool,∀ f∈F,SourceTensorClosure (matchingImage opposite) f.2 := by
  obtain ⟨opposite,c,_,line⟩ := WEscape.isotropic_orientation A.matrix
    (isotropic_first_nonzero A iso) iso
  refine ⟨opposite,?_⟩
  intro f hf
  have h := closed_action_matching A opposite c line (rows f hf)
  simpa only [InvertibleKernel.action_symm_action] using h

theorem tract_of_closed_coordinates (A : Holant.Tractable.InvertibleKernel)
    (iso : A.matrix false false^2+A.matrix true false^2=0)
    (F : Holant.SignatureFamily AlgebraicComplex) (finite : F.Finite)
    (rows : ∀ f∈F,Closed (A.symm.action f.2)) : Holant.Tractable.Tract F := by
  obtain ⟨opposite,all⟩ := closed_coordinates_matching A iso F rows
  refine ⟨finite.subset (fun _ h => h.1),?_⟩
  apply Or.inr
  apply Or.inr
  apply Or.inr
  apply Or.inl
  cases opposite
  · exact Or.inl (fun f hf => all f hf.1)
  · exact Or.inr (fun f hf => all f hf.1)

end
end Paper2.Paper1Proved.OddUnary.NR

