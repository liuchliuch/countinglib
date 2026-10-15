import Paper2.Paper1Accepted

/-! Source-exact initial branches consumed in Paper 2 Section 9.
Official Paper 1 arXiv:2609.00219v1, PDF p.39, Theorems 2.17 and 2.18,
independently rechecked 2026-10-09.  These are transparent accepted parameters,
not Paper 2 mountain/relative-EO conclusions.  Preprocessing is explicit. -/
namespace Paper2
open Tractable ExactInput

structure Paper1OddAccepted where
  /-- Theorem 2.18's ordinary-coordinate hardness half. -/
  odd_2_18 : ∀ L : Language, Preprocessed L.family →
    (∃ g ∈ L.family, Odd g.1 ∧ g.2 ≠ 0) →
    ¬ Tract L.family → Problem.SharpPHard .ordinary L

structure Paper1SingleWeightAccepted where
  /-- Theorem 2.17, retaining the exact two source exceptions. -/
  singleWeight_2_17 : ∀ L : Language, Preprocessed L.family →
    (∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d) →
    ¬ ((CommonOneSided L.family ∧ EOTract (centralFamily L.family)) ∨
      (BothChargeSigns L.family ∧ EOTract (completionFamily L.family))) →
    Problem.SharpPHard .nativeX L

end Paper2
