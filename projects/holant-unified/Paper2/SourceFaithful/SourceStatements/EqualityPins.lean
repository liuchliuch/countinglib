import Paper2.Paper1ProvedFactorProvider
import Paper2.Paper1ProvedOccurrenceProvider
import Paper2.SourceFaithful.RelativeEO.ComplementaryExit
import Paper2.RelativeEO.GeneralizedEqualityGadget
import Paper2.DegreeCSP.Model

/-! The native-X arm of source Corollary 3.5.  Its convention is finite
Turing-equivalent enlargement, rather than direct pin realizability.  The
original language may contain zero and nullary rows: only the two factors
actually being extracted are required to be nonzero and positive-arity. -/
namespace Paper2.SourceFaithful.SourceStatements.EqualityPins
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO Paper2.Paper1Proved
open Holant.LocalDrafts.Hardness.GeneralExtraction
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

private def pin (b : Bool) : AnySignature AlgebraicComplex :=
  ⟨1,TensorDecomposition.literalPin b⟩

private def pair (b : Bool) : Signature AlgebraicComplex 2 :=
  Signature.tensor (TensorDecomposition.literalPin b) (TensorDecomposition.literalPin (!b))

private theorem pair_apply (b : Bool) (x : Fin 2 → Bool) :
    pair b x = (if x 0 = b then 1 else 0) * (if x 1 = !b then 1 else 0) := rfl

private theorem pair_false : pair false = directedPair := by
  funext x
  rw [pair_apply]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [directedPair,h0,h1]

private theorem pair_realized (L : Language)
    (hp : (⟨2,directedPair⟩ : AnySignature AlgebraicComplex) ∈ L.family) (b : Bool) :
    NativeNetworkRealizesUpTo L.family (pair b) := by
  cases b with
  | false => rw [pair_false]; exact NativeNetworkRealizesUpTo.of_mem hp
  | true =>
    obtain ⟨N,hU,hX,c,hc,hN⟩ := NativeNetworkRealizesUpTo.of_mem hp
    let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
    refine ⟨N.reindexBoundary e,hU,hX,c,hc,?_⟩
    rw [Network.denote_reindexBoundary,hN]
    funext x
    rw [pair_apply]
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [Tensor.reindex,e,directedPair,h0,h1]

/-- Extract just the two literal factors of the directed pair.  Unlike whole
factor saturation, this actual finite macro catalogue needs no preprocessing
hypothesis on unrelated original rows. -/
theorem directedPair_supplies_pins (L : Language)
    (htwo : ¬ CommonOneSided L.family)
    (hp : (⟨2,directedPair⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language, M.family = L.family ∪ Set.range pin ∧
      FixedFieldOutput.Reduces .nativeX M L := by
  let added : Bool → AnySignature AlgebraicComplex := fun b => ⟨2,pair b⟩
  obtain ⟨B,hB⟩ := Language.coverage_family (L.family ∪ Set.range added)
    (L.family_finite.union (Set.finite_range _))
  have hLB : L.family ⊆ B.family := by rw [hB]; exact Set.subset_union_left
  have hBL : FixedFieldOutput.Reduces .nativeX B L :=
    directGadgetProvider.directGadget_2_5 L B hLB (by
      rw [hB]
      rintro f (hf | ⟨b,rfl⟩)
      · exact NativeNetworkRealizesUpTo.of_mem hf
      · exact pair_realized L hp b)
  have ht : ¬ Holant.Tractable.CommonOneSided B.family := by
    intro hs
    apply htwo
    rcases hs with hs | hs
    · left; intro f hf x hx; exact hs f (hLB hf) x hx
    · right; intro f hf x hx; exact hs f (hLB hf) x hx
  have hm := GeneralPowerExposure.mixedSupport_of_source ht
  rw [← FactorProvider.FiniteAugmentation.base_family B pin] at hm
  have powers : ∀ b : Bool, Nonempty (GeneralPowerExposure.PowerMacro
      (FactorProvider.FiniteAugmentation.base B pin) (pin b).2) := by
    intro b
    apply GeneralPowerExposure.labelled_power _ (by norm_num) hm
      (TensorDecomposition.literalPin b) (TensorDecomposition.literalPin (!b))
      (by decide) (TensorDecomposition.literalPin_ne_zero (!b))
    rw [FactorProvider.FiniteAugmentation.base_family]
    rw [hB]
    exact Or.inr ⟨b,rfl⟩
  obtain ⟨M,hM⟩ := Language.coverage_family (L.family ∪ Set.range pin)
    (L.family_finite.union (Set.finite_range _))
  refine ⟨M,hM,(FactorProvider.FiniteAugmentation.reduction B pin powers M ?_).trans hBL⟩
  rw [hM]
  exact Set.union_subset_union_left _ hLB

theorem complementaryE_supplies_pins (L : Language)
    (htwo : ¬ CommonOneSided L.family)
    (hE : (⟨4,complementaryE⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language, M.family = L.family ∪ Set.range pin ∧
      FixedFieldOutput.Reduces .nativeX M L := by
  let B := tagged L directedPair
  have hLB : L.family ⊆ B.family := by rw [tagged_family]; exact Set.subset_insert _ _
  have hp : (⟨2,directedPair⟩ : AnySignature AlgebraicComplex) ∈ B.family := by
    rw [tagged_family]; exact Set.mem_insert _ _
  obtain ⟨N,hN,hNB⟩ := directedPair_supplies_pins B
    (fun hs => htwo (hs.mono_family hLB)) hp
  obtain ⟨M,hM⟩ := Language.coverage_family (L.family ∪ Set.range pin)
    (L.family_finite.union (Set.finite_range _))
  have hMN : M.family ⊆ N.family := by rw [hM,hN]; exact Set.union_subset_union_left _ hLB
  exact ⟨M,hM,(restriction M N hMN).trans
    (hNB.trans (SourceFaithful.RelativeEO.directedPair_access_of_complementaryE
      occurrenceProvider L hE))⟩

private theorem equality_eq_generalized (d : ℕ) :
    DegreeCSP.equality (K := AlgebraicComplex) d = generalizedEquality 1 1 := by
  funext x
  exact DegreeCSP.equality_eq d x

/-- Literal source Corollary 3.5 for K-Holant.  Both directions are executed
fixed-field reductions, and every original zero/nullary row is retained. -/
theorem corollary_3_5_native (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language,
      M.family = L.family ∪ Set.range (fun b : Bool =>
        (⟨1,TensorDecomposition.literalPin b⟩ : AnySignature AlgebraicComplex)) ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  have hne : (fun _ : Fin d => false) ≠ (fun _ => true) := by
    intro h
    exact Bool.false_ne_true (congrFun h ⟨0,by omega⟩)
  have hfalse : DegreeCSP.equality (K := AlgebraicComplex) d (fun _ => false) ≠ 0 := by
    rw [equality_eq_generalized]
    simp [generalizedEquality,hne]
  have htrue : DegreeCSP.equality (K := AlgebraicComplex) d (fun _ => true) ≠ 0 := by
    rw [equality_eq_generalized]
    simp [generalizedEquality,Ne.symm hne]
  have htwo : ¬ CommonOneSided L.family := by
    rintro (h | h)
    · have hh := h _ heq (fun _ => false) hfalse
      simp [Paper2.charge,Paper2.weight] at hh
      omega
    · have hh := h _ heq (fun _ => true) htrue
      simp [Paper2.charge,Paper2.weight] at hh
      omega
  let i : Fin d := ⟨0,by omega⟩
  let j : Fin d := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [i,j] at this; omega
  have hr := gramTable_realized i j hij _ heq
  rw [equality_eq_generalized,generalizedEquality_gram_formula (by omega)] at hr
  simp only [one_mul] at hr
  obtain ⟨B,hB,hBL⟩ := directGadgetProvider.adjoin L complementaryE hr
  have hLB : L.family ⊆ B.family := by rw [hB]; exact Set.subset_insert _ _
  have hE : (⟨4,complementaryE⟩ : AnySignature AlgebraicComplex) ∈ B.family := by
    rw [hB]; exact Set.mem_insert _ _
  obtain ⟨N,hN,hNB⟩ := complementaryE_supplies_pins B
    (fun hs => htwo (hs.mono_family hLB)) hE
  obtain ⟨M,hM⟩ := Language.coverage_family (L.family ∪ Set.range pin)
    (L.family_finite.union (Set.finite_range _))
  have hMN : M.family ⊆ N.family := by rw [hM,hN]; exact Set.union_subset_union_left _ hLB
  have hLM : L.family ⊆ M.family := by rw [hM]; exact Set.subset_union_left
  exact ⟨M,hM,(restriction M N hMN).trans (hNB.trans hBL),restriction L M hLM⟩

end
end Paper2.SourceFaithful.SourceStatements.EqualityPins

