import Paper2.Tractable.Conformal.CommonBasis

/-! Definition 2.7: the ordinary common-basis condition and its presentation
in the fixed K coordinates are equivalent.  The project's normalized source K
satisfies KᵀK=X literally, so this bridge is valid for every target class; it
also covers the manuscript's scalar- and port-permutation-closed classes. -/
namespace Paper2.SourceFaithful.SourceStatements.CommonKBasis
open Paper2.Tractable
noncomputable section

/-- With M=K U, one and the same U transforms both the native X edge and every
signature already expressed in K coordinates. -/
theorem common_basis_comp_iff (C F : Paper2.SignatureFamily AlgebraicComplex)
    (U : InvertibleKernel) :
    IsCommonBasis C F (sourceKBasis.comp U) ↔
      IsCommonKBasis C (kCoordinates F) U := by
  have hedge : Paper2.Kernel.pullback Paper2.Signature.equality
      (sourceKBasis.comp U).matrix =
      Paper2.Kernel.pullback Paper2.Signature.disequality U.matrix := by
    simp only [InvertibleKernel.comp, pullback_mul, sourceKBasis_pullback]
  constructor
  · rintro ⟨he,hf⟩
    refine ⟨by simpa only [hedge] using he, ?_⟩
    rintro g ⟨f,hfmem,rfl⟩
    simpa only [InvertibleKernel.comp_symm, InvertibleKernel.comp_action] using hf f hfmem
  · rintro ⟨he,hf⟩
    refine ⟨by simpa only [hedge] using he, ?_⟩
    intro f hfmem
    have hmem : (⟨f.1,sourceKBasis.symm.action f.2⟩ : Paper2.AnySignature AlgebraicComplex)
        ∈ kCoordinates F := ⟨f,hfmem,rfl⟩
    simpa only [InvertibleKernel.comp_symm, InvertibleKernel.comp_action] using hf _ hmem

/-- The original-coordinate K predicate is exactly the in-K-coordinate
predicate on the explicitly computed family K⁻¹F. -/
theorem commonKPresentation_iff_inKCoordinates
    (C F : Paper2.SignatureFamily AlgebraicComplex) :
    CommonKPresentation C F ↔
      CommonKPresentationInKCoordinates C (kCoordinates F) := by
  constructor
  · rintro ⟨hfin,U,he,hf⟩
    refine ⟨(Conformal.familyAction_finite_iff sourceKBasis.symm F).mpr hfin,U,he,?_⟩
    rintro g ⟨f,hfmem,rfl⟩
    exact hf f hfmem
  · rintro ⟨hfin,U,he,hf⟩
    refine ⟨(Conformal.familyAction_finite_iff sourceKBasis.symm F).mp hfin,U,he,?_⟩
    intro f hfmem
    exact hf _ ⟨f,hfmem,rfl⟩

/-- The explicit equivalence stated in Definition 2.7, including finiteness,
the shared invertible matrix, and the mandatory simultaneous edge condition. -/
theorem commonTransformable_iff_inKCoordinates
    (C F : Paper2.SignatureFamily AlgebraicComplex) :
    CommonTransformable C F ↔
      CommonKPresentationInKCoordinates C (kCoordinates F) :=
  (commonTransformable_iff_commonKPresentation C F).trans
    (commonKPresentation_iff_inKCoordinates C F)

/-- Conversely, a family Γ already in K coordinates has the K presentation
exactly when KΓ has the ordinary common-basis presentation. -/
theorem inKCoordinates_iff_commonTransformable
    (C Gamma : Paper2.SignatureFamily AlgebraicComplex) :
    CommonKPresentationInKCoordinates C Gamma ↔
      CommonTransformable C (familyAction sourceKBasis Gamma) := by
  simpa only [Conformal.kCoordinates_familyAction] using
    (commonTransformable_iff_inKCoordinates C (familyAction sourceKBasis Gamma)).symm


end
end Paper2.SourceFaithful.SourceStatements.CommonKBasis
