import Paper2.SourceFaithful.SourceStatements.FactorExtractionCore
import Paper2.Paper1ProvedInterpolationProvider
import Paper2.RelativeEO.RankOneExit

/-! Literal Lemma 3.1: both the singular-factor arm and the infinite-projective
order arm use proved finite machines. Membership after factor closure means
membership in an explicitly described finite equivalent enlargement; it does
not mean that the original input dictionary already contains the factors. -/
namespace Paper2.SourceFaithful.SourceStatements.BinaryInterpolation
noncomputable section
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup
open Paper2.Paper1Proved
set_option backward.isDefEq.respectTransparency false

private theorem not_one_sided {F : SignatureFamily AlgebraicComplex}
    (h : BothChargeSigns F) : ¬ CommonOneSided F := by
  rcases h with ⟨⟨f,hf,x,hx,hn⟩,⟨g,hg,y,hy,hp⟩⟩
  rintro (hs | hs)
  · exact (not_le_of_gt hn) (hs f hf x hx)
  · exact (not_le_of_gt hp) (hs g hg y hy)

/-- The displayed nonzero unary factors are both available through actual
strict reductions, with no prime-factor or preprocessing certificate. -/
theorem source_3_1_singular (L : Language) (hboth : BothChargeSigns L.family)
    (B : Binary (K := AlgebraicComplex))
    (hmem : (⟨2,matrixSignature B⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (u v : Signature AlgebraicComplex 1) (hu : u ≠ 0) (hv : v ≠ 0)
    (hfactor : matrixSignature B = Signature.tensor u v) :
    ∃ M : Language,
      M.family = insert (⟨1,v⟩ : AnySignature AlgebraicComplex)
        (insert (⟨1,u⟩ : AnySignature AlgebraicComplex) L.family) ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  have hm : (⟨2,Signature.tensor u v⟩ : AnySignature AlgebraicComplex) ∈ L.family :=
    hfactor ▸ hmem
  obtain ⟨M,hM,hML,hLM⟩ := FactorExtraction.pair_access L u v
    (ordered_tensor_ne_zero u v hu hv) hm (not_one_sided hboth)
  exact ⟨M,hM,PublicReduction.of_fixed_field .nativeX M L hML,
    PublicReduction.of_fixed_field .nativeX L M hLM⟩

/-- Infinite projective order supplies a literal nonzero rank-one binary in
an exact finite equivalent enlargement. The original positive chain queries,
interpolation postprocessor, and fixed-field/public root converters are all
executed. Both charge signs are needed only when its factors are extracted. -/
theorem source_3_1_infinite_order (L : Language)
    (B : Binary (K := AlgebraicComplex))
    (hmem : (⟨2,matrixSignature B⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hdet : Matrix.det (transfer B) ≠ 0) (hinf : ¬ ProjectivelyFinite (transfer B)) :
    ∃ (u v : Signature AlgebraicComplex 1) (M : Language),
      u ≠ 0 ∧ v ≠ 0 ∧
      M.family = insert (⟨2,Signature.tensor u v⟩ : AnySignature AlgebraicComplex) L.family ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  obtain ⟨u,v,M,hu,hv,hM,hML⟩ := InterpolationProvider.infiniteOrder L B hmem hdet hinf
  have hLM : L.family ⊆ M.family := by
    rw [hM]
    exact Set.subset_insert _ _
  exact ⟨u,v,M,hu,hv,hM,PublicReduction.of_fixed_field .nativeX M L hML,
    PublicReduction.of_fixed_field .nativeX L M (restriction L M hLM)⟩

/-- Both clauses of source Lemma 3.1, with its original common charge-sign
hypothesis and literal ordered binary. The infinite-order conclusion is
expressed by two nonzero ordered unary tensor factors, hence has rank one. -/
theorem source_3_1 (L : Language) (hboth : BothChargeSigns L.family)
    (B : Binary (K := AlgebraicComplex))
    (hmem : (⟨2,matrixSignature B⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    (∀ (u v : Signature AlgebraicComplex 1), u ≠ 0 → v ≠ 0 →
      matrixSignature B = Signature.tensor u v →
      ∃ M : Language,
        M.family = insert (⟨1,v⟩ : AnySignature AlgebraicComplex)
          (insert (⟨1,u⟩ : AnySignature AlgebraicComplex) L.family) ∧
        Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M) ∧
    (Matrix.det (transfer B) ≠ 0 → ¬ ProjectivelyFinite (transfer B) →
      ∃ (u v : Signature AlgebraicComplex 1) (M : Language), u ≠ 0 ∧ v ≠ 0 ∧
        M.family = insert (⟨2,Signature.tensor u v⟩ : AnySignature AlgebraicComplex) L.family ∧
        Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M) :=
  ⟨fun u v hu hv hf => source_3_1_singular L hboth B hmem u v hu hv hf,
    source_3_1_infinite_order L B hmem⟩

end
end Paper2.SourceFaithful.SourceStatements.BinaryInterpolation

