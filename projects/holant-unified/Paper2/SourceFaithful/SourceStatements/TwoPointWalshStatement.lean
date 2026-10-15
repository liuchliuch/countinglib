import Paper2.SourceFaithful.SourceStatements.TwoPointWalsh
import Paper2.SourceFaithful.SourceStatements.TwoPointWalshFactorAccess
import Paper2.SourceFaithful.SourceStatements.PublicReduction
import Paper2.PublicDichotomyComplete

/-! Source Lemma 3.15 with its original tensor-factor hypothesis. The finite
equivalent stage retains the original language, its specified source table is
nonzero, and its arbitrary ordered tensor decomposition retains its full unit
scale. Factor extraction uses an actual no-identity power-exposure programme;
neither preprocessing nor a separately available tensor factor is assumed.

The classification conclusion is an instance of the independently completed
native dichotomy. The additional root-of-unity anchor is proved constructively
from the given factor, with the fixed basis U = K and all graph scales retained.
-/
namespace Paper2.SourceFaithful.SourceStatements.TwoPointWalsh
open Paper2.Tractable Paper2.ExactInput Paper2.HeightOne.PhaseCards
open Paper2.HighHeightNormalization
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Literal meaning of a finite equivalent enlargement containing a nonzero
signature with the stated ordered two-point Walsh tensor factor. -/
structure FactorStage (L : Language) where
  language : Language
  retained : L.family ⊆ language.family
  backward : Problem.Reduces .nativeX language L
  forward : Problem.Reduces .nativeX L language
  sourceArity : ℕ
  decomposition : TensorDecomposition AlgebraicComplex sourceArity
  sourceNonzero : decomposition.value ≠ 0
  sourceMember : (⟨sourceArity,decomposition.value⟩ : AnySignature AlgebraicComplex) ∈
    language.family
  selected : Fin decomposition.count
  arityAtLeastFour : 4 ≤ decomposition.arity selected
  arityEven : Even (decomposition.arity selected)
  word : Fin (decomposition.arity selected) → Bool
  first : AlgebraicComplex
  second : AlgebraicComplex
  firstNonzero : first ≠ 0
  secondNonzero : second ≠ 0
  walshExact : walshCoordinates (decomposition.factor selected) =
    twoPointForm word first second

def HasKAnchor (N : Language) : Prop :=
  ∃ (g : Signature AlgebraicComplex 4) (lam : AlgebraicComplex),
    (⟨4,g⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧ lam ≠ 0 ∧
    Kernel.pullback Signature.disequality sourceKBasis.inverse = Signature.equality ∧
    sourceKBasis.action g = fun x => lam * equalityFour x

lemma retained_not_oneSided (L : Language) (S : FactorStage L)
    (hboth : BothChargeSigns L.family) : ¬ CommonOneSided S.language.family := by
  obtain ⟨⟨f,hf,x,hx,hneg⟩,⟨g,hg,y,hy,hpos⟩⟩ := hboth
  intro hs
  rcases hs with hs | hs
  · exact (not_le_of_gt hneg) (hs f (S.retained hf) x hx)
  · exact (not_le_of_gt hpos) (hs g (S.retained hg) y hy)

/-- The stronger, constructive root-of-unity conclusion of source 3.15.
The selected factor is first extracted by a true controlled reduction.
The two-copy and self-loop phase-order graphs then produce the literal K
anchor in a finite equivalent enlargement of the ORIGINAL language. -/
theorem factor_stage_root_anchor (L : Language) (hboth : BothChargeSigns L.family)
    (S : FactorStage L) (ell : ℕ) (hell : 0 < ell)
    (hroot : (S.second/S.first)^ell = 1) :
    ∃ N : Language, L.family ⊆ N.family ∧
      Problem.Reduces .nativeX N L ∧ Problem.Reduces .nativeX L N ∧
      HasKAnchor N := by
  obtain ⟨M,hM,hMS,hSM⟩ := TwoPointWalshFactorAccess.factor_access S.language
    S.decomposition S.selected S.sourceNonzero S.sourceMember
    (retained_not_oneSided L S hboth)
  have hSMsub : S.language.family ⊆ M.family := by rw [hM]; exact Set.subset_insert _ _
  have hmem : (⟨S.decomposition.arity S.selected,S.decomposition.factor S.selected⟩ :
      AnySignature AlgebraicComplex) ∈ M.family := by rw [hM]; exact Set.mem_insert _ _
  obtain ⟨N,g,lam,hN,hNM,hMN,hlam,hedge,hanchor⟩ := root_anchor_enlargement M
    S.arityAtLeastFour S.arityEven (S.decomposition.factor S.selected)
    (supplied_realizable hmem) S.word S.first S.second S.firstNonzero S.secondNonzero
    S.walshExact ell hell hroot
  have hMNsub : M.family ⊆ N.family := by rw [hN]; exact Set.subset_insert _ _
  have hSL := PublicReduction.to_fixed_field .nativeX S.language L S.backward
  have hLS := PublicReduction.to_fixed_field .nativeX L S.language S.forward
  refine ⟨N,S.retained.trans (hSMsub.trans hMNsub),
    PublicReduction.of_fixed_field .nativeX N L ((hNM.trans hMS).trans hSL),
    PublicReduction.of_fixed_field .nativeX L N (hLS.trans (hSM.trans hMN)),?_⟩
  exact ⟨g,lam,by rw [hN]; exact Set.mem_insert _ _,hlam,hedge,hanchor⟩

/-- Literal source Lemma 3.15. Both the hardness disjunction and the finite
equivalent enlargement use the strict public root answer convention, including
arbitrary correct bounded oracle answers. Its equality anchor has U = K,
edge scale one, and a recorded nonzero quaternary scale.
-/
theorem source_3_15 (L : Language) (hboth : BothChargeSigns L.family) (S : FactorStage L) :
    (Problem.SharpPHard .nativeX L ∨ Tract (kImage L)) ∧
      ((∃ ell : ℕ, 0 < ell ∧ (S.second/S.first)^ell = 1) →
        ∃ N : Language, L.family ⊆ N.family ∧
          Problem.Reduces .nativeX N L ∧ Problem.Reduces .nativeX L N ∧
          HasKAnchor N) := by
  refine ⟨?_,?_⟩
  · by_cases ht : Tract (kImage L)
    · exact Or.inr ht
    · exact Or.inl (PublicDichotomy.native_hardness L ht)
  · rintro ⟨ell,hell,hroot⟩
    exact factor_stage_root_anchor L hboth S ell hell hroot

end
end Paper2.SourceFaithful.SourceStatements.TwoPointWalsh

