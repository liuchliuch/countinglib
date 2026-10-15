import Paper2.Paper1ProvedGadgetProvider
import Mathlib.Data.Fintype.BigOperators

/-! A literal factor block and its full ordered remainder. The original
normalization scalar is absorbed into that remainder; the source tensor is
obtained by a genuine single-vertex boundary reindexing. -/
namespace Paper2.Paper1Proved.TensorSplit
open Paper2.Tractable Paper2.ExactInput
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [CommMonoidWithZero K] {n : ℕ}
variable (D : TensorDecomposition K n) (j : Fin D.count)

abbrev Other := {i : Fin D.count // i ≠ j}
abbrev OtherPorts := Σ i : Other D j, Fin (D.arity i.val)
def remainderArity : ℕ := Fintype.card (OtherPorts D j)
def remainder (y : Fin (remainderArity D j) → Bool) : K :=
  (D.scale : K) * ∏ i : Other D j, D.factor i.val
    (fun k => y ((Fintype.equivFin (OtherPorts D j)) ⟨i,k⟩))

def portSplit : (Fin (D.arity j) ⊕ OtherPorts D j) ≃ (Σ i : Fin D.count, Fin (D.arity i)) where
  toFun := Sum.elim (fun k => ⟨j,k⟩) (fun p => ⟨p.1.val,p.2⟩)
  invFun p := if hi : p.1 = j then .inl (Fin.cast (congrArg D.arity hi) p.2)
    else .inr ⟨⟨p.1,hi⟩,p.2⟩
  left_inv := by
    intro p
    cases p with
    | inl k => simp
    | inr p => simp [p.1.property]
  right_inv := by
    rintro ⟨i,k⟩
    by_cases hi : i = j
    · subst i; simp
    · simp [hi]

def splitPorts : Fin (D.arity j + remainderArity D j) ≃ Fin n :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin (OtherPorts D j)).symm).trans
    ((portSplit D j).trans D.ports))

@[simp] theorem split_factor (k : Fin (D.arity j)) :
    (splitPorts D j).symm (D.ports ⟨j,k⟩) = Fin.castAdd (remainderArity D j) k := by
  simp [splitPorts,portSplit,Equiv.sumCongr,Sum.map]
@[simp] theorem split_other (i : Other D j) (k : Fin (D.arity i.val)) :
    (splitPorts D j).symm (D.ports ⟨i.val,k⟩) =
      Fin.natAdd (D.arity j) ((Fintype.equivFin (OtherPorts D j)) ⟨i,k⟩) := by
  simp [splitPorts,portSplit,Equiv.sumCongr,Sum.map,i.property]

 theorem tensor_factor_remainder :
    Signature.tensor (D.factor j) (remainder D j) = Tensor.reindex (splitPorts D j).symm D.value := by
  funext x
  simp only [Signature.tensor_apply,remainder,Tensor.reindex_apply,TensorDecomposition.value]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp only [split_factor,split_other]
  ac_rfl

 theorem remainder_positive (hcount : 2 ≤ D.count) (hpos : ∀ i, 0 < D.arity i) :
    0 < remainderArity D j := by
  let i : Fin D.count := if hj : j.val = 0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have hi : i ≠ j := by
    intro hi
    have hv := congrArg Fin.val hi
    by_cases hj : j.val = 0
    · simpa [i,hj] using hv
    · have hh : 0 = j.val := by simpa [i,hj] using hv
      exact hj hh.symm
  let p : OtherPorts D j := ⟨⟨i,hi⟩,⟨0,hpos i⟩⟩
  letI : Nonempty (OtherPorts D j) := ⟨p⟩
  exact Fintype.card_pos

section Field
variable [Nontrivial K] [NoZeroDivisors K]
 theorem remainder_nonzero (hn : ∀ i, D.factor i ≠ 0) : remainder D j ≠ 0 := by
  have hw : ∀ i : Other D j, ∃ x, D.factor i.val x ≠ 0 := by
    intro i
    by_contra hh
    apply hn i.val
    funext x
    simpa only [Pi.zero_apply] using not_not.mp (not_exists.mp hh x)
  choose x hx using hw
  let y : Fin (remainderArity D j) → Bool := fun k =>
    x ((Fintype.equivFin (OtherPorts D j)).symm k).1
      ((Fintype.equivFin (OtherPorts D j)).symm k).2
  have hp : remainder D j y ≠ 0 := by
    unfold remainder
    apply mul_ne_zero (Units.ne_zero D.scale)
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hh : (fun k => y ((Fintype.equivFin (OtherPorts D j)) ⟨i,k⟩)) = x i := by
      funext k
      exact congrArg (fun p : OtherPorts D j => x p.1 p.2)
        ((Fintype.equivFin (OtherPorts D j)).symm_apply_apply ⟨i,k⟩)
    rw [hh]
    exact hx i
  intro hz
  exact hp (congrFun hz y)
end Field

 theorem singleton_unique (hcount : D.count = 1) (i : Fin D.count) : i = j := by
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  omega

def singletonPorts (hcount : D.count = 1) : Fin (D.arity j) ≃ Fin n where
  toFun k := D.ports ⟨j,k⟩
  invFun p := Fin.cast (congrArg D.arity (singleton_unique D j hcount (D.ports.symm p).1))
    (D.ports.symm p).2
  left_inv k := by
    apply Fin.ext
    exact congrArg (fun p : Σ i : Fin D.count, Fin (D.arity i) => p.2.val)
      (D.ports.symm_apply_apply ⟨j,k⟩)
  right_inv p := by
    obtain ⟨⟨i,k⟩,rfl⟩ := D.ports.surjective p
    have hi := singleton_unique D j hcount i
    subst i
    apply congrArg (fun k : Fin (D.arity j) => D.ports ⟨j,k⟩)
    apply Fin.ext
    exact congrArg (fun p : Σ i : Fin D.count, Fin (D.arity i) => p.2.val)
      (D.ports.symm_apply_apply ⟨j,k⟩)

@[simp] theorem singleton_factor (hcount : D.count = 1) (k : Fin (D.arity j)) :
    (singletonPorts D j hcount).symm (D.ports ⟨j,k⟩) = k := by
  apply Fin.ext
  exact congrArg (fun p : Σ i : Fin D.count, Fin (D.arity i) => p.2.val)
    (D.ports.symm_apply_apply ⟨j,k⟩)

 theorem singleton_exact (hcount : D.count = 1) :
    Tensor.reindex (singletonPorts D j hcount).symm D.value =
      fun x => (D.scale : K) * D.factor j x := by
  letI : IsEmpty (Other D j) := ⟨fun i => i.property (singleton_unique D j hcount i.val)⟩
  funext x
  simp only [Tensor.reindex_apply,TensorDecomposition.value]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp [singleton_factor]

 theorem reindex_realized (L : Language)
    (D : TensorDecomposition AlgebraicComplex n) (j : Fin D.count)
    (hroot : (⟨n,D.value⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    NativeNetworkRealizesUpTo L.family (Signature.tensor (D.factor j) (remainder D j)) := by
  obtain ⟨N,hU,hX,c,hc,hd⟩ := NativeNetworkRealizesUpTo.of_mem hroot
  refine ⟨N.reindexBoundary (splitPorts D j).symm,hU.reindexBoundary _,hX.reindexBoundary _,c,hc,?_⟩
  rw [Network.denote_reindexBoundary,hd,tensor_factor_remainder]
  rfl

 theorem singleton_realized (L : Language)
    (D : TensorDecomposition AlgebraicComplex n) (j : Fin D.count)
    (hcount : D.count = 1)
    (hroot : (⟨n,D.value⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    NativeNetworkRealizesUpTo L.family (D.factor j) := by
  obtain ⟨N,hU,hX,c,hc,hd⟩ := NativeNetworkRealizesUpTo.of_mem hroot
  refine ⟨N.reindexBoundary (singletonPorts D j hcount).symm,
    hU.reindexBoundary _,hX.reindexBoundary _,c * (D.scale : AlgebraicComplex),
    mul_ne_zero hc (Units.ne_zero D.scale),?_⟩
  rw [Network.denote_reindexBoundary,hd]
  have he := singleton_exact D j hcount
  funext x
  have hh := congrFun he x
  change c * D.value (fun k => x ((singletonPorts D j hcount).symm k)) = _
  rw [show D.value (fun k => x ((singletonPorts D j hcount).symm k)) =
    (D.scale : AlgebraicComplex) * D.factor j x from hh]
  exact (mul_assoc _ _ _).symm

end
end Paper2.Paper1Proved.TensorSplit
