import Paper2.RelativeEO.DirectedPairFactors
import Paper2.SourceFaithful.FactorClosure

/-! Canonical fixed-field answer version of the proved local construction.
The pure signatures/networks are unchanged. Machine reductions are proved again
from the separately named source-exact records; no output-code conversion or
old strict-root classification is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO

theorem directedPair_factorClosure (P : Paper1FactorClosureAccepted) (L : Language)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hpair : (⟨2, directedPair⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language, L.family ⊆ M.family ∧
      (⟨1, TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      (⟨1, TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨M, hsub, hfactor, hm, hs, hML, hLM⟩ :=
    factorClosure_with_member_decomposition P L hpre htwo directedPair hpair
      directedPairDecomposition directedPairDecomposition_value
      directedPairDecomposition_positive directedPairDecomposition_prime
  exact ⟨M, hsub, hfactor (0 : Fin 2), hfactor (1 : Fin 2), hm, hs, hML, hLM⟩


end Paper2.SourceFaithful.RelativeEO
