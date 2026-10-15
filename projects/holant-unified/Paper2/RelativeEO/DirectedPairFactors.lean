import Paper2.RelativeEO.DirectedPair
import Paper2.PrimeFactorization.PointMass

/-! Both literal pins arise by the authorized factor-extraction theorem after
unrestricted Δ access. They are not silently declared native-X gadgets. -/
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput
open scoped BigOperators

noncomputable def directedPairDecomposition : TensorDecomposition AlgebraicComplex 2 where
  count := 2
  arity _ := 1
  factor i := TensorDecomposition.literalPin (i == 1)
  ports := {
    toFun p := p.1
    invFun i := ⟨i, 0⟩
    left_inv := by rintro ⟨i, j⟩; have hj : j = 0 := Fin.eq_zero j; subst j; rfl
    right_inv := fun _ => rfl }
  scale := 1

theorem directedPairDecomposition_value : directedPairDecomposition.value = directedPair := by
  funext x
  change (1 : AlgebraicComplex) * (∏ i : Fin 2,
    TensorDecomposition.literalPin (i == 1) (fun _ => x i)) = directedPair x
  rw [Fin.prod_univ_two]
  simp only [one_mul]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [TensorDecomposition.literalPin, directedPair, h0, h1]

theorem directedPairDecomposition_positive (i : Fin directedPairDecomposition.count) :
    0 < directedPairDecomposition.arity i := Nat.zero_lt_one

theorem directedPairDecomposition_prime (i : Fin directedPairDecomposition.count) :
    TensorPrime (directedPairDecomposition.factor i) :=
  TensorDecomposition.literalPin_prime _

/-- Retained actual factor extraction of Δ produces both ordered unit pins,
with full original-language containment and two real machine reductions. -/
theorem directedPair_factorClosure (P : Paper1FactorClosureAccepted) (L : Language)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hpair : (⟨2, directedPair⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language, L.family ⊆ M.family ∧
      (⟨1, TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      (⟨1, TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  obtain ⟨M, hsub, hfactor, hm, hs, hML, hLM⟩ :=
    factorClosure_with_member_decomposition P L hpre htwo directedPair hpair
      directedPairDecomposition directedPairDecomposition_value
      directedPairDecomposition_positive directedPairDecomposition_prime
  exact ⟨M, hsub, hfactor (0 : Fin 2), hfactor (1 : Fin 2), hm, hs, hML, hLM⟩

end Paper2.RelativeEO
