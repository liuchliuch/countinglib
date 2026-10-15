import Paper2.SourceFaithful.LocalInputs
import Paper2.PrimeFactorization

/-! Additive coordinate-output adapters; the ordered prime decompositions are
reused from the proved pure mathematics, not assumed as a machine result. -/
namespace Paper2.SourceFaithful
open Tractable ExactInput

/-- Paper 1 factor extraction now has a proved decomposition input for every
preprocessed language; its retained two-sided-family hypothesis is unchanged. -/
theorem factorClosure_exists (P : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family) :
    ∃ (D : PrimeFactorization L) (M : Language), M.family = L.family ∪ D.factors ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  let D := PrimeFactorization.ofPreprocessed L hL
  obtain ⟨M, hM, hML, hLM⟩ := P.factorClosure_2_19 L hL htwo D
  exact ⟨D, M, hM, hML, hLM⟩

/-- Retained factor extraction with a prescribed member decomposition. This is
an actual finite exact-input augmentation, with enough invariants for iterating
factor extraction while keeping all original labels. -/
theorem factorClosure_with_member_decomposition (P : Paper1FactorClosureAccepted)
    (L : Language) (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (Q : TensorDecomposition AlgebraicComplex n) (hQ : Q.value = f)
    (hp : ∀ j, 0 < Q.arity j) (ht : ∀ j, TensorPrime (Q.factor j)) :
    ∃ M : Language, L.family ⊆ M.family ∧
      (∀ j, (⟨Q.arity j, Q.factor j⟩ : AnySignature AlgebraicComplex) ∈ M.family) ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨D, hD⟩ := PrimeFactorization.exists_with_member_decomposition L hL f hf Q hQ hp ht
  obtain ⟨M, hM, hML, hLM⟩ := P.factorClosure_2_19 L hL htwo D
  have hsub : L.family ⊆ M.family := by rw [hM]; exact Set.subset_union_left
  refine ⟨M, hsub, ?_, ?_, ?_, hML, hLM⟩
  · intro j
    rw [hM]
    exact Or.inr (hD j)
  · rw [hM]
    exact D.retained_preprocessed hL
  · intro hs
    apply htwo
    rcases hs with hs | hs
    · exact Or.inl (fun g hg => hs g (hsub hg))
    · exact Or.inr (fun g hg => hs g (hsub hg))

end Paper2.SourceFaithful
