import Paper2.DegreeCSP.BooleanSupport
import Paper2.Paper1ProvedOddUnaryGeneralizedEqualityNormalize

/-! Exact final algebra in the primary degree-CSP exceptional classes.
Any one shared nonzero diagonal affine chart suffices, so in particular all
literal phase classes A^r_k of the primary Theorem 22 are included. This result
constructs the mandatory edge witness and does not infer classes from runtime. -/
namespace Paper2.DegreeCSP
open Tractable
noncomputable section
namespace ClassesToTract
open Paper1Proved.OddUnary.GeneralizedEqualityNormalize

/-- The binary native-X edge itself belongs to the affine class. -/
theorem affine_native_edge : Affine (kernelSignature Signature.disequality) := by
  have h : BooleanStructure.Preserves BooleanStructure.xor3
      BooleanStructure.disequalityRelation := by
    intro x hx y hy z hz
    have he (x : Fin 2 → Bool) (hx : x ∈ BooleanStructure.disequalityRelation) : x 1 = !(x 0) := by
      change x 0 ≠ x 1 at hx
      cases h0 : x 0 <;> cases h1 : x 1 <;> simp_all
    change Bool.xor (Bool.xor (x 0) (y 0)) (z 0) ≠
      Bool.xor (Bool.xor (x 1) (y 1)) (z 1)
    rw [he x hx,he y hy,he z hz]
    cases x 0 <;> cases y 0 <;> cases z 0 <;> decide
  convert BooleanStructure.affine_indicator_of_xor BooleanStructure.disequalityRelation h using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [BooleanStructure.indicator,BooleanStructure.disequalityRelation,
      kernelSignature,Signature.disequality,h0,h1]

/-- A class containing the native edge and the entire native family has the
literal one common K-basis in the computational coordinates. -/
theorem native_common_basis (C F : SignatureFamily AlgebraicComplex) (hfin : F.Finite)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ C)
    (hF : F ⊆ C) : CommonTransformable C (familyAction sourceKBasis F) := by
  refine ⟨hfin.image _,sourceKBasis,?_,?_⟩
  · simpa only [sourceKBasis_pullback] using hX
  · rintro f ⟨g,hg,rfl⟩
    simpa only [InvertibleKernel.symm_action_action,Sigma.eta] using hF hg

private theorem tract_affine {F : SignatureFamily AlgebraicComplex}
    (h : CommonTransformable affineClass F) : Tract F := by
  refine ⟨h.1.subset (fun _ hf => hf.1),?_⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    (h.mono_family (fun _ hf => hf.1))))))

private theorem tract_product {F : SignatureFamily AlgebraicComplex}
    (h : CommonTransformable productClass F) : Tract F := by
  refine ⟨h.1.subset (fun _ hf => hf.1),?_⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    (h.mono_family (fun _ hf => hf.1)))))))

/-- The true product exception of the degree-CSP theorem gives source clause 6. -/
theorem product_family (F : SignatureFamily AlgebraicComplex) (hfin : F.Finite)
    (hP : ∀ f ∈ F, Product f.2) : Tract (familyAction sourceKBasis F) := by
  apply tract_product
  exact native_common_basis productClass F hfin (product_disequality (0 : Fin 2) 1)
    (fun f hf => hP f hf)

/-- The true affine exception gives source clause 5, with the actual X edge. -/
theorem affine_family (F : SignatureFamily AlgebraicComplex) (hfin : F.Finite)
    (hA : ∀ f ∈ F, Affine f.2) : Tract (familyAction sourceKBasis F) := by
  apply tract_affine
  exact native_common_basis affineClass F hfin affine_native_edge (fun f hf => hA f hf)

/-- One shared diagonal chart, not different charts for different signatures. -/
def SharedDiagonalAffine (F : SignatureFamily AlgebraicComplex) : Prop :=
  ∃ t : AlgebraicComplex, ∃ ht : t ≠ 0,
    ∀ f ∈ F, Affine ((diagonal t ht).action f.2)

/-- A common phase twist is a genuine common-basis affine exception. The
phase's root order is unnecessary for this implication. -/
theorem diagonal_affine_family (F : SignatureFamily AlgebraicComplex) (hfin : F.Finite)
    (hA : SharedDiagonalAffine F) : Tract (familyAction sourceKBasis F) := by
  obtain ⟨t,ht,hA⟩ := hA
  apply (xConformal_tract_iff (diagonal_conformal t ht) F).mpr
  apply affine_family _ (hfin.image _)
  rintro f ⟨g,hg,rfl⟩
  exact hA g hg

/-- The literal diagonal image used in the primary classes A^r_k. A
primitive 4k-th root raised to the chosen r is one instance of t. -/
def PhaseAffineFamily (t : AlgebraicComplex) (F : SignatureFamily AlgebraicComplex) : Prop :=
  ∀ f ∈ F, ∃ g : Signature AlgebraicComplex f.1,
    Affine g ∧ f.2 = Signature.coordinateAction (fun _ => diagonalKernel 1 t) g

/-- The complementary diagonal multiplies every original coefficient by t^n. -/
theorem diagonal_phase_cancel (t : AlgebraicComplex) (ht : t ≠ 0) {n : ℕ}
    (g : Signature AlgebraicComplex n) :
    (diagonal t ht).action (Signature.coordinateAction (fun _ => diagonalKernel 1 t) g) =
      fun x => t ^ n * g x := by
  change Signature.coordinateAction (fun _ => diagonalKernel t 1)
    (Signature.coordinateAction (fun _ => diagonalKernel 1 t) g) = _
  rw [Signature.coordinateAction_comp]
  have hm : Kernel.mul (diagonalKernel t 1) (diagonalKernel 1 t) = diagonalKernel t t := by
    funext a b
    cases a <;> cases b <;> simp [Kernel.mul_apply,diagonalKernel]
  simp only [hm]
  rw [coordinateAction_diagonal]
  funext x
  simp [diagonalCoefficient]

/-- All A^r_k exceptions from the primary theorem have one literal common
nonzero diagonal affine chart and hence satisfy the original criterion. -/
theorem phase_affine_family (F : SignatureFamily AlgebraicComplex) (hfin : F.Finite)
    (t : AlgebraicComplex) (ht : t ≠ 0) (hA : PhaseAffineFamily t F) :
    Tract (familyAction sourceKBasis F) := by
  apply diagonal_affine_family F hfin
  refine ⟨t,ht,?_⟩
  intro f hf
  obtain ⟨g,hg,he⟩ := hA f hf
  rw [he,diagonal_phase_cancel t ht g]
  exact hg.scale (t ^ f.1)

/-- This is exactly the contradiction needed after the genuine degree-CSP
classification has supplied P or its one common diagonal affine class. -/
theorem exceptional_family (F : SignatureFamily AlgebraicComplex) (hfin : F.Finite)
    (h : (∀ f ∈ F, Product f.2) ∨ SharedDiagonalAffine F) :
    Tract (familyAction sourceKBasis F) := by
  rcases h with h | h
  · exact product_family F hfin h
  · exact diagonal_affine_family F hfin h

end ClassesToTract
end
end Paper2.DegreeCSP
