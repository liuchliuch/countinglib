import Paper2.ExactInput.GadgetAugmentation

/-! Exact accepted factor-saturation interface. The hypothesis is a real ordered
tensor-prime decomposition and a retained, not-common-one-sided original family.
No inference of free pins from a formal tensor factor is built into definitions. -/
namespace Paper2
open Tractable ExactInput

/-- All factors, all ordered port blocks, and the nonzero normalization scalar
are retained explicitly in `TensorDecomposition`; every factor has positive arity. -/
structure PrimeFactorization (L : Language) where
  decomposition : (i : Fin L.count) → TensorDecomposition AlgebraicComplex (L.arity i.val)
  exact_value : ∀ i, (decomposition i).value = L.signature i
  positive : ∀ i j, 0 < (decomposition i).arity j
  prime : ∀ i j, TensorPrime ((decomposition i).factor j)

namespace PrimeFactorization

def Index {L : Language} (D : PrimeFactorization L) :=
  Σ i : Fin L.count, Fin (D.decomposition i).count

instance {L : Language} (D : PrimeFactorization L) : Fintype D.Index :=
  inferInstanceAs (Fintype (Σ i : Fin L.count, Fin (D.decomposition i).count))

noncomputable def factors {L : Language} (D : PrimeFactorization L) : SignatureFamily AlgebraicComplex :=
  Set.range (fun ij : D.Index =>
    (⟨(D.decomposition ij.1).arity ij.2, (D.decomposition ij.1).factor ij.2⟩ : AnySignature AlgebraicComplex))

theorem factors_finite {L : Language} (D : PrimeFactorization L) : D.factors.Finite :=
  Set.finite_range _

end PrimeFactorization

/-- A nonzero unary is genuinely tensor-prime; there is no positive two-block cut. -/
theorem unary_tensorPrime (f : Signature AlgebraicComplex 1) (hf : f ≠ 0) : TensorPrime f := by
  refine ⟨hf, ?_⟩
  intro m k hm hk e
  have hc := Fintype.card_congr e
  simp only [Fintype.card_fin] at hc
  omega

/-- Exactly Paper 1 v1 Lemma 2.23, restated by Paper 2 Lemma 2.19.
The augmentation is the retained union, not a replacement by factors alone. -/
structure Paper1FactorClosureAccepted where
  factorClosure_2_23 : ∀ L : Language, Preprocessed L.family →
    ¬ CommonOneSided L.family → ∀ D : PrimeFactorization L, ∀ M : Language,
      M.family = L.family ∪ D.factors →
        Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M

namespace Paper1FactorClosureAccepted

/-- A real literal-input finite augmentation, with the source's exact equivalence. -/
theorem factorClosure_2_19 (P : Paper1FactorClosureAccepted) (L : Language)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (D : PrimeFactorization L) :
    ∃ M : Language, M.family = L.family ∪ D.factors ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  obtain ⟨M, hM⟩ := Language.coverage_family _ (L.family_finite.union D.factors_finite)
  exact ⟨M, hM, P.factorClosure_2_23 L hpre htwo D M hM⟩

end Paper1FactorClosureAccepted
end Paper2
