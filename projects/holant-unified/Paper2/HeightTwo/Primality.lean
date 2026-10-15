import Paper2.HeightTwo.Normalization

/-! Nonsingular weighted equalities are genuinely tensor-prime. -/
namespace Paper2.HeightTwo
open Tractable

lemma weightedEquality_evenSupport (f : Signature AlgebraicComplex 2)
    (hf : WeightedEquality f) : EvenSupport f := by
  intro x hx
  have he : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  rw [he] at hx ⊢
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp only [h0, h1] at hx ⊢
  · decide
  · exact False.elim (hx hf.1)
  · exact False.elim (hx hf.2.1)
  · decide

lemma weightedEquality_tensorPrime (f : Signature AlgebraicComplex 2)
    (hf : WeightedEquality f) : TensorPrime f := by
  have h0 : f (fun _ => false) ≠ 0 := by
    rw [weightedEquality_table f hf]
    simpa [kernelSignature, diagonalKernel] using hf.2.2.1
  have h1 : f (fun _ => true) ≠ 0 := by
    rw [weightedEquality_table f hf]
    simpa [kernelSignature, diagonalKernel] using hf.2.2.2
  refine ⟨?_, ?_⟩
  · intro hz
    exact h0 (congrFun hz _)
  · intro m k hm hk e a b he
    have hcard : m + k = 2 := by simpa using Fintype.card_congr e
    have ht : EvenSupport (Tensor.tensor a b) := by
      apply (evenSupport_reindex_iff finSumFinEquiv _).mp
      apply (evenSupport_reindex_iff e _).mp
      change EvenSupport (Tensor.reindex e (Signature.tensor a b))
      rw [he]
      exact weightedEquality_evenSupport f hf
    have hz : Tensor.reindex e (Signature.tensor a b) (fun _ => false) ≠ 0 := by
      simpa only [he] using h0
    have ho : Tensor.reindex e (Signature.tensor a b) (fun _ => true) ≠ 0 := by
      simpa only [he] using h1
    obtain ⟨ha, hb⟩ := factor_evenSupport a b ht
      (left_ne_zero_of_mul hz) (right_ne_zero_of_mul hz)
    have hme : Even m := by
      simpa using even_arity_of_endpoints a ha (left_ne_zero_of_mul ho)
    have hke : Even k := by
      simpa using even_arity_of_endpoints b hb (right_ne_zero_of_mul ho)
    obtain ⟨r, hr⟩ := hme
    obtain ⟨s, hs⟩ := hke
    omega

end Paper2.HeightTwo
