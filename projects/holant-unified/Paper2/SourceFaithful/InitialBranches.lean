import Paper2.SourceFaithful.Paper1Accepted

/-! Source-exact Theorems 2.17 and 2.18 under fixed-field coordinate outputs.
All preprocessing and the two distinct single-layer exceptions are retained. -/
namespace Paper2.SourceFaithful
open Tractable ExactInput

structure Paper1OddAccepted where
  odd_2_18 : ∀ L : Language, Preprocessed L.family →
    (∃ g ∈ L.family, Odd g.1 ∧ g.2 ≠ 0) →
    ¬ Tract L.family → FixedFieldOutput.SharpPHard .ordinary L

structure Paper1SingleWeightAccepted where
  singleWeight_2_17 : ∀ L : Language, Preprocessed L.family →
    (∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d) →
    ¬ ((CommonOneSided L.family ∧ EOTract (centralFamily L.family)) ∨
      (BothChargeSigns L.family ∧ EOTract (completionFamily L.family))) →
    FixedFieldOutput.SharpPHard .nativeX L

end Paper2.SourceFaithful
