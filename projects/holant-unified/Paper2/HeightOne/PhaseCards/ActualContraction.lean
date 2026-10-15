import Paper2.HeightOne.PhaseCards.Coordinates

/-! The binary contraction card is a genuine two-vertex, two-native-edge outer
network. Substitution compiles arbitrary actual f and B witnesses into it. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
attribute [local instance] Classical.propDecidable
open Tractable GroupSplit GroupSplit.MatrixGroup
open scoped BigOperators
variable {ι : Type} [Fintype ι]

abbrev closeArity (ι : Type) [Fintype ι] : Bool → ℕ
  | false => Fintype.card ι + 2
  | true => 2

def closePorts (ι : Type) [Fintype ι] :
    (Σ v : Bool, Fin (closeArity ι v)) ≃ (Fin (Fintype.card ι) ⊕ (Bool × Bool)) where
  toFun
    | ⟨false, i⟩ => Sum.elim (fun j => .inl ((Fintype.equivFin ι) j))
        (fun b => .inr (b, false)) (NetworkRealizable.frontPair ι i)
    | ⟨true, i⟩ => .inr (finTwoEquiv i, true)
  invFun
    | .inl i => ⟨false, (NetworkRealizable.frontPair ι).symm
        (.inl ((Fintype.equivFin ι).symm i))⟩
    | .inr (b, false) => ⟨false, (NetworkRealizable.frontPair ι).symm (.inr b)⟩
    | .inr (b, true) => ⟨true, finTwoEquiv.symm b⟩
  left_inv := by
    rintro ⟨v, i⟩
    cases v with
    | false =>
      cases h : NetworkRealizable.frontPair ι i with
      | inl j =>
        simp [h]
        exact (Equiv.symm_apply_eq _).mpr h.symm
      | inr b =>
        simp [h]
        exact (Equiv.symm_apply_eq _).mpr h.symm
    | true => simp
  right_inv := by
    rintro (i | ⟨b, c⟩)
    · simp
    · cases c <;> simp

def closeOuter (f : Tensor AlgebraicComplex (ι ⊕ Bool)) (B : AMat) :
    FiniteNetwork AlgebraicComplex Bool Bool (Fintype.card ι) where
  arity := closeArity ι
  ports := closePorts ι
  vertex
    | false => Tensor.reindex (NetworkRealizable.frontPair ι).symm f
    | true => binarySignature B
  edge := fun _ => Signature.disequality

lemma closeOuter_denote (f : Tensor AlgebraicComplex (ι ⊕ Bool)) (B : AMat) :
    Tensor.reindex (Fintype.equivFin ι).symm (closeOuter f B).toNetwork.denote =
      contractKernel (nativeKernel B) f := by
  classical
  rw [FiniteNetwork.denote_toNetwork]
  funext x
  rw [Tensor.reindex_apply, FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  unfold contractKernel
  refine Finset.sum_congr (by ext; simp) ?_
  intro z _
  have hn : nativeKernel B (z false) (z true) = B (!(z false)) (!(z true)) :=
    Kernel.disequality_sandwich B _ _
  rw [hn]
  simp only [Fintype.prod_bool, closeOuter, binarySignature, Tensor.reindex]
  congr 1
  congr 1
  funext p
  cases p with
  | inl i =>
    simp only [closePorts, Equiv.coe_fn_mk]
    rw [Equiv.apply_symm_apply]
    simp
  | inr b =>
    simp only [closePorts, Equiv.coe_fn_mk]
    rw [Equiv.apply_symm_apply]
    rfl

/-- Attaching an actual ordered binary to the two distinguished ports uses two
literal native-X edges and only the original source resources. -/
theorem actual_contractKernel {F : SignatureFamily AlgebraicComplex}
    {f : Tensor AlgebraicComplex (ι ⊕ Bool)} {B : AMat}
    (hf : NetworkRealizable F f) (hB : NetworkRealizable F (binarySignature B)) :
    NetworkRealizable F (contractKernel (nativeKernel B) f) := by
  rw [← closeOuter_denote]
  apply NetworkRealizable.reindex
  apply NetworkRealizable.substitute
  · intro e; rfl
  · intro v
    change NetworkRealizable F ((closeOuter f B).vertex ((Fintype.equivFin Bool).symm v))
    cases (Fintype.equivFin Bool).symm v
    · exact hf.reindex _
    · exact hB

end
end Paper2.HeightOne.PhaseCards
