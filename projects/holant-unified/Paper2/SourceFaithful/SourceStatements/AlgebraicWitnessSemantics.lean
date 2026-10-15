import Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessReturned
import Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessRuntimeSource

/-! The exact class interpretation of the arbitrary-edge recognition body.
The point in these statements is retained, so the result applies to the
matrix coordinates emitted by the real witness program. -/
namespace Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessRuntime
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
open AlgebraicWitness (Class ComplexMember)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def point (C : Class) (d : Data)
    (z : Fin (OriginalVariableLayout.Width (OriginalAffineSystem.Entries d.arity)
      (parameterCount C d)) → ℂ) :=
  OriginalTensorRows.point d.arity (parameterCount C d) id z

def matrixAt (C : Class) (d : Data)
    (z : Fin (OriginalVariableLayout.Width (OriginalAffineSystem.Entries d.arity)
      (parameterCount C d)) → ℂ) := SymbolicTransform.matrix (point C d z)

def inverseAt (C : Class) (d : Data)
    (z : Fin (OriginalVariableLayout.Width (OriginalAffineSystem.Entries d.arity)
      (parameterCount C d)) → ℂ) := SymbolicTransform.inverse (point C d z)

/-- Every satisfying point describes the source classes at its own matrix
and inverse, including every local-affine support inequation. -/
theorem classes_of_zero (C : Class) (d : Data)
    (z : Fin (OriginalVariableLayout.Width (OriginalAffineSystem.Entries d.arity)
      (parameterCount C d)) → ℂ)
    (hb : ∀ i, z (bindings C d i) = (values d i : ℂ))
    (hz : ∀ p ∈ typedBody C d,
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p = 0) :
    (∀ i, ComplexMember C (Signature.coordinateAction (fun _ => inverseAt C d z)
      (fun x => (d.G i x : ℂ)))) ∧
    ComplexMember C (fun x : Fin 2 → Bool =>
      Kernel.pullback (fun a b => (d.E a b : ℂ)) (matrixAt C d z) (x 0) (x 1)) := by
  have hbound : ∀ i, z (bindings C d i) =
      OriginalVariableLayout.boundValues
        (fun j => (AlgebraicWitness.values d.arity d.G d.E j : ℂ)) i := by
    intro i
    rw [←congrFun (OriginalAffineDecision.originalValues_coe d.arity _) i]
    exact hb i
  cases C with
  | affine =>
    obtain ⟨B,hB⟩ := RawAffineRecognitionSource.combined_zero_iff d.arity d.input z |>.mp hz
    have he := (OriginalAffineSystem.body_source_iff d.arity
      (AlgebraicWitness.values d.arity d.G d.E) z hbound B).mp hB |>.2
    simp only [AlgebraicWitness.sourceVertex_values,AlgebraicWitness.sourceEdge_values] at he
    have hi : SymbolicTransform.inverse (OriginalAffineSystem.point d.arity z) =
        inverseAt .affine d z := by funext a b; rfl
    have hu : SymbolicTransform.matrix (OriginalAffineSystem.point d.arity z) =
        matrixAt .affine d z := by funext a b; rfl
    constructor
    · intro i
      apply (ExtensionAffine.affine_iff (algebraMap AlgebraicComplex ℂ) _).mpr
      refine ⟨B.1 i,OriginalAffineSystem.point d.arity z (.inr (.inl i)),?_⟩
      funext x
      have hx := he (.inr (.inl ⟨i,x⟩))
      simpa only [AffineBranch.equations,MvPolynomial.eval₂_sub,
        MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,MvPolynomial.eval₂_C,
        SymbolicTransform.eval_vertex,hi,ExtensionAffine.formula,sub_eq_zero,
        IntermediateField.algebraMap_apply,Holant.Signature.coordinateAction,
        Paper2.Signature.coordinateAction,Holant.Kernel.pullback,Paper2.Kernel.pullback,
        Holant.Kernel.mul,Paper2.Kernel.mul,Holant.Kernel.transpose,Paper2.Kernel.transpose] using hx
    · apply (ExtensionAffine.affine_iff (algebraMap AlgebraicComplex ℂ) _).mpr
      refine ⟨B.2,OriginalAffineSystem.point d.arity z (.inr (.inr ())),?_⟩
      funext x
      have hx := he (.inr (.inr x))
      simpa only [AffineBranch.equations,MvPolynomial.eval₂_sub,
        MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,MvPolynomial.eval₂_C,
        SymbolicTransform.eval_edge,hu,ExtensionAffine.formula,sub_eq_zero,
        IntermediateField.algebraMap_apply,Holant.Signature.coordinateAction,
        Paper2.Signature.coordinateAction,Holant.Kernel.pullback,Paper2.Kernel.pullback,
        Holant.Kernel.mul,Paper2.Kernel.mul,Holant.Kernel.transpose,Paper2.Kernel.transpose] using hx
  | product =>
    obtain ⟨B,hB⟩ := RawProductRecognitionSource.combined_zero_iff d.arity d.input z |>.mp hz
    have he := (OriginalProductSystem.body_source_iff d.arity
      (AlgebraicWitness.values d.arity d.G d.E) z hbound B).mp hB
    simp only [AlgebraicWitness.sourceVertex_values,AlgebraicWitness.sourceEdge_values] at he
    have ht (j : ProductVariableLayout.Slot d.count) :
        ExtensionSource.ProductOver (ProductBranch.transformed d.G d.E
          (algebraMap AlgebraicComplex ℂ)
          (SymbolicTransform.matrix (OriginalProductSystem.point d.arity z))
          (SymbolicTransform.inverse (OriginalProductSystem.point d.arity z)) j) := by
      apply (ExtensionSource.productOver_iff _).mpr
      refine ⟨B j,fun p => OriginalProductSystem.point d.arity z (.inr ⟨j,p⟩),?_⟩
      rw [←ProductBranch.evaluated_at]
      funext x
      have hx := he (.inr ⟨j,x⟩)
      simpa [ProductBranch.equations,ProductBranch.eval_template,
        ProductBranch.evaluated,sub_eq_zero] using hx
    exact ⟨fun i => ht (.inl i),ht (.inr ())⟩
  | localAffine =>
    obtain ⟨B,hB⟩ := RawLocalAffineRecognitionSource.combined_zero_iff d.arity d.input z |>.mp hz
    obtain ⟨he,hn⟩ := OriginalLocalAffineSystem.constraints_of_zero d.arity
      (AlgebraicWitness.values d.arity d.G d.E) z hbound B hB
    simp only [AlgebraicWitness.sourceVertex_values,AlgebraicWitness.sourceEdge_values] at he hn
    obtain ⟨_,hm⟩ := (LocalAffineBranch.constraints_iff d.G d.E
      (algebraMap AlgebraicComplex ℂ) B (OriginalLocalAffineSystem.point d.arity z)).mp ⟨he,hn⟩
    have ht (j : ProductVariableLayout.Slot d.count) :
        ExtensionLocalAffine.LocalAffineOver (algebraMap AlgebraicComplex ℂ)
          (LocalAffineBranch.transformed d.G d.E (algebraMap AlgebraicComplex ℂ)
            (SymbolicTransform.matrix (OriginalLocalAffineSystem.point d.arity z))
            (SymbolicTransform.inverse (OriginalLocalAffineSystem.point d.arity z)) j) := by
      rw [←LocalAffineBranch.evaluated_at]
      exact (ExtensionLocalAffine.localAffine_iff _ _).mpr ⟨B j,_,hm j⟩
    exact ⟨fun i => ht (.inl i),ht (.inr ())⟩

/-- The actual terminating witness program accepts exactly the displayed
common complex transform problem, with an arbitrary algebraic original edge. -/
theorem accepts_iff (C : Class) (d : Data) :
    (output C d).isSome = true ↔ AlgebraicWitness.ComplexWitness C d.G d.E := by
  rw [output_correct]
  have hv : (fun i => (values d i : ℂ)) = OriginalVariableLayout.boundValues
      (fun j => (AlgebraicWitness.values d.arity d.G d.E j : ℂ)) :=
    OriginalAffineDecision.originalValues_coe d.arity _
  simp_rw [congrFun hv]
  cases C with
  | affine =>
    simpa only [typedBody,bindings,parameterCount,OriginalAffineSystem.Bound,
      AlgebraicWitness.sourceVertex_values,AlgebraicWitness.sourceEdge_values,
      AffineBranch.Shared,AlgebraicWitness.ComplexWitness,AlgebraicWitness.ComplexMember,
      IntermediateField.algebraMap_apply] using
      RawAffineRecognitionSource.bound_solution_iff d.arity d.input
        (AlgebraicWitness.values d.arity d.G d.E)
  | product =>
    have h := RawProductRecognitionSource.bound_solution_iff d.arity d.input
      (AlgebraicWitness.values d.arity d.G d.E)
    simp only [AlgebraicWitness.sourceVertex_values,AlgebraicWitness.sourceEdge_values] at h
    have hs : ProductBranch.SharedSource d.G d.E (algebraMap AlgebraicComplex ℂ) ↔
        AlgebraicWitness.ComplexWitness .product d.G d.E := by
      constructor
      · rintro ⟨U,V,hU,hV,ht⟩
        exact ⟨U,V,hU,hV,fun i => ht (.inl i),ht (.inr ())⟩
      · rintro ⟨U,V,hU,hV,hG,hE⟩
        refine ⟨U,V,hU,hV,?_⟩
        rintro (i | u)
        · exact hG i
        · exact hE
    exact h.trans hs
  | localAffine =>
    have h := RawLocalAffineRecognitionSource.bound_solution_iff d.arity d.input
      (AlgebraicWitness.values d.arity d.G d.E)
    simp only [AlgebraicWitness.sourceVertex_values,AlgebraicWitness.sourceEdge_values] at h
    have hs : LocalAffineBranch.Shared d.G d.E (algebraMap AlgebraicComplex ℂ) ↔
        AlgebraicWitness.ComplexWitness .localAffine d.G d.E := by
      constructor
      · rintro ⟨U,V,hU,hV,ht⟩
        exact ⟨U,V,hU,hV,fun i => ht (.inl i),ht (.inr ())⟩
      · rintro ⟨U,V,hU,hV,hG,hE⟩
        refine ⟨U,V,hU,hV,?_⟩
        rintro (i | u)
        · exact hG i
        · exact hE
    exact h.trans hs

end
end Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessRuntime

