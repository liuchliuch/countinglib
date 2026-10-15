import Paper2.Paper1ProvedFactorProvider
import Paper2.SourceFaithful.GadgetAugmentation

/-! Access to one specified nonzero tensor factor by an actual finite
equivalent-language augmentation. Unrelated zero or nullary language members
are allowed; nullary factors of the selected tensor retain their full scalar. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.SourceStatements.TwoPointWalshFactorAccess
noncomputable section
open Paper2.Tractable Paper2.ExactInput Paper2.Paper1Proved
open Holant.LocalDrafts.Hardness.GeneralExtraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem factors_nonzero (D : TensorDecomposition AlgebraicComplex n) (hD : D.value ≠ 0)
    (i : Fin D.count) : D.factor i ≠ 0 := by
  classical
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hD
  intro hi
  have hp : (∏ j, D.factor j (fun k => x (D.ports ⟨j,k⟩))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (congrFun hi _)
  exact hx (by simp [TensorDecomposition.value,hp])

/-- No boundary remains outside the chosen factor. The actual graph is the
original one-vertex graph with its ports reordered, and its scalar contains
the complete nullary remainder. -/
theorem nullary_remainder_realized (L : Language)
    (D : TensorDecomposition AlgebraicComplex n) (j : Fin D.count)
    (hD : D.value ≠ 0)
    (hroot : (⟨n,D.value⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hr : TensorSplit.remainderArity D j = 0) :
    NativeNetworkRealizesUpTo L.family (D.factor j) := by
  classical
  let g := TensorSplit.remainder D j
  have hg : g ≠ 0 := TensorSplit.remainder_nonzero D j (factors_nonzero D hD)
  have hw (y : Fin (TensorSplit.remainderArity D j) → Bool) : y = fun _ => false := by
    funext i
    have hi := i.isLt
    omega
  have hg0 : g (fun _ => false) ≠ 0 := by
    intro hz
    apply hg
    funext y
    rw [hw y]
    exact hz
  let e : Fin (D.arity j + TensorSplit.remainderArity D j) ≃ Fin (D.arity j) :=
    finCongr (by omega)
  obtain ⟨N,hU,hX,c,hc,hN⟩ := TensorSplit.reindex_realized L D j hroot
  refine ⟨N.reindexBoundary e,hU.reindexBoundary e,hX.reindexBoundary e,
    c * g (fun _ => false),mul_ne_zero hc hg0,?_⟩
  rw [Network.denote_reindexBoundary,hN]
  funext x
  change c * (D.factor j (fun i => x (e (Fin.castAdd _ i))) *
    g (fun i => x (e (Fin.natAdd _ i)))) = _
  have he : (fun i : Fin (D.arity j) => x (e (Fin.castAdd _ i))) = x := by
    funext i
    exact congrArg x (Fin.ext rfl)
  rw [he,hw (fun i => x (e (Fin.natAdd _ i)))]
  ring

private def factorItem (D : TensorDecomposition AlgebraicComplex n) (j : Fin D.count) :
    Unit → AnySignature AlgebraicComplex := fun _ => ⟨D.arity j,D.factor j⟩

/-- The positive-remainder extraction uses an actual labelled power exposure
macro, followed by the controlled finite-catalogue interpolation reduction. -/
theorem positive_remainder_access (L : Language)
    (D : TensorDecomposition AlgebraicComplex n) (j : Fin D.count)
    (hD : D.value ≠ 0)
    (hroot : (⟨n,D.value⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (htwo : ¬ CommonOneSided L.family)
    (hr : 0 < TensorSplit.remainderArity D j) :
    ∃ M : Language,
      M.family = insert (⟨D.arity j,D.factor j⟩ : AnySignature AlgebraicComplex) L.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  classical
  let h := D.factor j
  let g := TensorSplit.remainder D j
  let added := factorItem D j
  obtain ⟨B,hB,hBL⟩ := directGadgetProvider.adjoin L (Signature.tensor h g)
    (TensorSplit.reindex_realized L D j hroot)
  have hLB : L.family ⊆ B.family := by
    rw [hB]
    exact Set.subset_insert _ _
  have ht : ¬ Holant.Tractable.CommonOneSided B.family := by
    intro hs
    apply htwo
    rcases hs with hs | hs
    · left; intro f hf x hx; exact hs f (hLB hf) x hx
    · right; intro f hf x hx; exact hs f (hLB hf) x hx
  have hm := GeneralPowerExposure.mixedSupport_of_source ht
  rw [← FactorProvider.FiniteAugmentation.base_family B added] at hm
  have powers : ∀ u : Unit, Nonempty (GeneralPowerExposure.PowerMacro
      (FactorProvider.FiniteAugmentation.base B added) (added u).2) := by
    intro u
    apply GeneralPowerExposure.labelled_power _ (by norm_num) hm h g hr
      (TensorSplit.remainder_nonzero D j (factors_nonzero D hD))
    rw [FactorProvider.FiniteAugmentation.base_family,hB]
    exact Set.mem_insert _ _
  obtain ⟨M,hM⟩ := Language.coverage_family
    (insert (⟨D.arity j,D.factor j⟩ : AnySignature AlgebraicComplex) L.family)
    (L.family_finite.insert _)
  have hML : FixedFieldOutput.Reduces .nativeX M L := by
    apply (FactorProvider.FiniteAugmentation.reduction B added powers M ?_).trans hBL
    rw [hM]
    rintro f (rfl | hf)
    · exact Or.inr ⟨(),rfl⟩
    · exact Or.inl (hLB hf)
  refine ⟨M,hM,hML,restriction L M ?_⟩
  rw [hM]
  exact Set.subset_insert _ _

/-- Any specified factor of a nonzero source tensor is available in a finite
equivalent enlargement. This requires no prime decomposition or preprocessing
of the original language, and includes a zero-arity selected factor. -/
theorem factor_access (L : Language)
    (D : TensorDecomposition AlgebraicComplex n) (j : Fin D.count)
    (hD : D.value ≠ 0)
    (hroot : (⟨n,D.value⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (htwo : ¬ CommonOneSided L.family) :
    ∃ M : Language,
      M.family = insert (⟨D.arity j,D.factor j⟩ : AnySignature AlgebraicComplex) L.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  by_cases hr : TensorSplit.remainderArity D j = 0
  · exact directGadgetProvider.adjoin_equivalence restrictionProvider L (D.factor j)
      (nullary_remainder_realized L D j hD hroot hr)
  · exact positive_remainder_access L D j hD hroot htwo (Nat.pos_of_ne_zero hr)

theorem factor_access_subset (L : Language)
    (D : TensorDecomposition AlgebraicComplex n) (j : Fin D.count)
    (hD : D.value ≠ 0)
    (hroot : (⟨n,D.value⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (htwo : ¬ CommonOneSided L.family) :
    ∃ M : Language, L.family ⊆ M.family ∧
      (⟨D.arity j,D.factor j⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨M,hM,hML,hLM⟩ := factor_access L D j hD hroot htwo
  refine ⟨M,?_,?_,hML,hLM⟩
  · rw [hM]; exact Set.subset_insert _ _
  · rw [hM]; exact Set.mem_insert _ _

end
end Paper2.SourceFaithful.SourceStatements.TwoPointWalshFactorAccess

