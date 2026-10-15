import Paper2.SourceFaithful.SourceStatements.FactorExtractionCore
import Paper2.SourceFaithful.SourceStatements.FactorExtractionOneSided

/-! Literal source Theorem 2.14. The original tensor and the two specified
factors determine the two exact finite dictionaries. Outside a common support
side they are strictly equivalent. The common-side exception uses the genuine
central EO criterion and retains all original zero/nullary rows in evaluation.
All output and oracle conventions are the public minimal-root convention. -/
namespace Paper2.SourceFaithful.SourceStatements.FactorExtraction
noncomputable section
open Paper2.Tractable Paper2.ExactInput
variable {m n : ℕ}

/-- Every clause of the printed tensor-factor extraction theorem, with no
prime-decomposition, preprocessing, or proof-provider hypothesis. -/
theorem source_2_14 (L M : Language) (F : SignatureFamily AlgebraicComplex)
    (a : Signature AlgebraicComplex m) (b : Signature AlgebraicComplex n)
    (hL : L.family = insert (⟨m+n,Signature.tensor a b⟩ : AnySignature AlgebraicComplex) F)
    (hM : M.family = insert (⟨m,a⟩ : AnySignature AlgebraicComplex)
      (insert (⟨n,b⟩ : AnySignature AlgebraicComplex) F))
    (hn : Signature.tensor a b ≠ 0) :
    (¬ CommonOneSided L.family →
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M) ∧
    (CommonOneSided L.family →
      (EOTract (centralFamily L.family) → Problem.InFP .nativeX L) ∧
      (¬ EOTract (centralFamily L.family) → Problem.SharpPHard .nativeX L)) :=
  ⟨source_2_14_equivalence L M F a b hL hM hn, common_side_exception L⟩

/-- No target dictionary has to be supplied: an exact finite representation
of Lambda+a+b is selected before any graph input is evaluated. -/
theorem source_2_14_exists (L : Language) (F : SignatureFamily AlgebraicComplex)
    (a : Signature AlgebraicComplex m) (b : Signature AlgebraicComplex n)
    (hL : L.family = insert (⟨m+n,Signature.tensor a b⟩ : AnySignature AlgebraicComplex) F)
    (hn : Signature.tensor a b ≠ 0) :
    ∃ M : Language,
      M.family = insert (⟨m,a⟩ : AnySignature AlgebraicComplex)
        (insert (⟨n,b⟩ : AnySignature AlgebraicComplex) F) ∧
      (¬ CommonOneSided L.family →
        Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M) ∧
      (CommonOneSided L.family →
        (EOTract (centralFamily L.family) → Problem.InFP .nativeX L) ∧
        (¬ EOTract (centralFamily L.family) → Problem.SharpPHard .nativeX L)) := by
  have hF : F.Finite := L.family_finite.subset (by rw [hL]; exact Set.subset_insert _ _)
  obtain ⟨M,hM⟩ := Language.coverage_family
    (insert (⟨m,a⟩ : AnySignature AlgebraicComplex)
      (insert (⟨n,b⟩ : AnySignature AlgebraicComplex) F))
    ((hF.insert _).insert _)
  exact ⟨M,hM,source_2_14 L M F a b hL hM hn⟩

end
end Paper2.SourceFaithful.SourceStatements.FactorExtraction

