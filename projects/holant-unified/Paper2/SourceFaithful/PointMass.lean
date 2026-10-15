import Paper2.SourceFaithful.FactorClosure
import Paper2.PrimeFactorization.PointMass

/-! Machine-dependent pin-extraction adapters, retaining the original exact
ordered decompositions and nonzero scalar normalization. -/
namespace Paper2.SourceFaithful
open Tractable ExactInput

/-- A nonzero pure point mass of positive arity yields a literal pin in a
retained exact-input augmentation via the separately accepted Paper 1 lemma. -/
theorem pointMass_factorClosure (P : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (b : Bool) {n : ℕ} (hn : 0 < n) (c : AlgebraicComplex) (hc : c ≠ 0)
    (hmem : (⟨n, ChargeBridge.pointMass b n c⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language, L.family ⊆ M.family ∧
      (⟨1, TensorDecomposition.literalPin b⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨M, hsub, hfactors, hpre, hside, hML, hLM⟩ :=
    factorClosure_with_member_decomposition P L hL htwo _ hmem
      (TensorDecomposition.pointMass b n c hc)
      (TensorDecomposition.value_pointMass b n c hc)
      (TensorDecomposition.pointMass_positive b n c hc)
      (TensorDecomposition.pointMass_prime b n c hc)
  exact ⟨M, hsub, hfactors ⟨0, hn⟩, hpre, hside, hML, hLM⟩

/-- Both pure point masses yield both literal pins, with actual machine
reductions composed through two retained factor augmentations. -/
theorem pointMass_pair_factorClosure (P : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (c d : AlgebraicComplex) (hc : c ≠ 0) (hd : d ≠ 0)
    (hzero : (⟨m, ChargeBridge.pointMass false m c⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hone : (⟨n, ChargeBridge.pointMass true n d⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language, L.family ⊆ M.family ∧
      (⟨1, TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      (⟨1, TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨A, hLA, hz, hpreA, hsideA, hAL, hLAred⟩ :=
    pointMass_factorClosure P L hL htwo false hm c hc hzero
  obtain ⟨M, hAM, ho, hpreM, hsideM, hMA, hAMred⟩ :=
    pointMass_factorClosure P A hpreA hsideA true hn d hd (hLA hone)
  exact ⟨M, hLA.trans hAM, hAM hz, ho, hpreM, hsideM,
    hMA.trans hAL, hLAred.trans hAMred⟩

end Paper2.SourceFaithful
