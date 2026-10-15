import Paper2.Tractable.Conformal

/-! Exact common native-K basis transport for the normalization ledger.
The returned witness is the literal product `A⁻¹ V`, including its edge
condition. Only closure under nonzero scalar multiplication is required. -/
namespace Paper2.SourceFaithful.SourceStatements.NormalizationLedger
noncomputable section
open Tractable Tractable.Conformal

def NonzeroScaleClosed (C : SignatureFamily AlgebraicComplex) : Prop :=
  ∀ n (f : Signature AlgebraicComplex n), (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ C →
    ∀ c : AlgebraicComplex, c ≠ 0 →
      (⟨n, fun x => c * f x⟩ : AnySignature AlgebraicComplex) ∈ C

lemma nonzeroScaleClosed_of_scaleClosed {C : SignatureFamily AlgebraicComplex}
    (hC : ScaleClosed C) : NonzeroScaleClosed C :=
  fun n f hf c _ => hC n f hf c

lemma conformal_identity : XConformal InvertibleKernel.identity := by
  refine ⟨1, one_ne_zero, ?_⟩
  simp [InvertibleKernel.identity, Kernel.pullback]

lemma conformal_comp {D A : InvertibleKernel} (hD : XConformal D)
    (hA : XConformal A) : XConformal (D.comp A) := by
  obtain ⟨d, hd, heD⟩ := hD
  obtain ⟨a, ha, heA⟩ := hA
  refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
  change Kernel.pullback Signature.disequality (Kernel.mul D.matrix A.matrix) = _
  rw [pullback_mul, heD, pullback_scale, heA]
  funext x y
  ring

/-- A single actual native-K basis is pulled back to precisely `A⁻¹ V`.
The original family is retained after the accumulated tensor action. -/
theorem commonKBasis_pullback {C G F : SignatureFamily AlgebraicComplex}
    (hC : NonzeroScaleClosed C) (A V : InvertibleKernel) (hA : XConformal A)
    (hretained : familyAction A G ⊆ F) (hV : IsCommonKBasis C F V) :
    IsCommonKBasis C G (A.symm.comp V) := by
  obtain ⟨a, ha, heA⟩ := hA
  refine ⟨?_, ?_⟩
  · change (⟨2, kernelSignature (Kernel.pullback Signature.disequality
        (Kernel.mul A.inverse V.matrix))⟩ : AnySignature AlgebraicComplex) ∈ C
    rw [pullback_mul, pullback_inverse _ A ha heA, pullback_scale]
    exact hC 2 _ hV.1 a⁻¹ (inv_ne_zero ha)
  · intro f hf
    have hv := hV.2 ⟨f.1, A.action f.2⟩ (hretained ⟨f, hf, rfl⟩)
    simpa only [InvertibleKernel.comp_symm, InvertibleKernel.comp_action,
      InvertibleKernel.symm_symm] using hv

/-- The source's final tractability implication follows from retained original
signatures and conformal invariance, with no terminal-class premise on the
normalization step. -/
theorem tract_pullback {G F : SignatureFamily AlgebraicComplex}
    (A : InvertibleKernel) (hA : XConformal A)
    (hretained : familyAction A G ⊆ F)
    (hF : Tract (familyAction sourceKBasis F)) :
    Tract (familyAction sourceKBasis G) := by
  apply (xConformal_tract_iff hA G).mpr
  exact hF.mono_family (familyAction_mono sourceKBasis hretained)

end
end Paper2.SourceFaithful.SourceStatements.NormalizationLedger

