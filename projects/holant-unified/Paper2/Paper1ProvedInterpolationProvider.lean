import Paper2.Paper1ProvedFactorProvider
import Paper2.SourceFaithful.OccurrenceInputs
import Holant.Proofs.BinaryInterpolation.SourceTransport
import Holant.Proofs.Algorithms.BinaryQueryControl

/-! Paper 1 Lemma 3.1 on the literal Paper 2 binary. The source spectral
pencil, positive chain queries, rational interpolation machine and every
query/output bound are the proved Paper 1 constructions. Its common complex
number field embeds faithfully in AlgebraicComplex before either graph input
is read. Exact finite label scanners and rational field converters then give
the canonical Paper 2 reduction. -/
namespace Paper2.Paper1Proved.InterpolationProvider
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.RelativeEO
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup
open Holant.Complexity.BinaryInterpolation Holant.Complexity.UniversalPairReduction
open Holant.LocalDrafts.BinaryInterpolation Holant.LocalDrafts.MainChain
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16384

variable (L : Language)
abbrev complexFamily := SourceTransport.family (signatures L)
abbrev complexAlgebraic := SourceTransport.family_algebraic (signatures L)
variable {B : Binary (K := AlgebraicComplex)}
variable (M : AlgebraicSource.Macro (complexFamily L) (SourceTransport.binary B))
variable (p : AlgebraicSource.Pencil M.binary)
abbrev field := FieldSource.Field (complexFamily L) M p
abbrev presentation := FieldSource.fixedField (complexFamily L) (complexAlgebraic L) M p

theorem field_algebraic : field L M p ≤ algebraicClosure ℚ ℂ := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨i,rfl⟩
  exact mem_algebraicClosure_iff.mpr
    (AlgebraicSource.CommonField.coefficient_algebraic (complexFamily L)
      (complexAlgebraic L) M.binary M.binary_algebraic p i)

def embedding : field L M p →ₐ[ℚ] AlgebraicComplex :=
  IntermediateField.inclusion (field_algebraic L M p)

@[simp] theorem embedding_complex (x : field L M p) :
    SourceTransport.inclusion (embedding L M p x) = (x : ℂ) := rfl

def right : Binary (K := AlgebraicComplex) :=
  (AlgebraicSource.CommonField.right (complexFamily L) M.binary p).map
    (embedding L M p).toRingHom

theorem right_complex : SourceTransport.binary (right L M p) = p.H := by
  ext a b
  exact AlgebraicSource.CommonField.right_exact (complexFamily L) M.binary p a b

theorem right_nonzero : right L M p ≠ 0 := by
  intro hz
  apply p.H_nonzero
  rw [← right_complex L M p,hz]
  ext a b
  exact map_zero SourceTransport.inclusion

theorem right_singular : Matrix.det (right L M p) = 0 := by
  have hd : Matrix.det p.H = 0 := by
    by_contra hd
    have hr := Matrix.rank_of_det_ne_zero hd
    rw [p.H_rank] at hr
    norm_num at hr
  apply SourceTransport.inclusion.injective
  rw [← SourceTransport.determinant_map,right_complex L M p,hd,map_zero]

abbrev adjoined := BinaryFamily.signatures (signatures L) (right L M p)

theorem adjoined_complex : SourceTransport.family (adjoined L M p) =
    BinaryFamily.signatures (complexFamily L) p.H := by
  funext i x
  unfold SourceTransport.family adjoined BinaryFamily.signatures
  split_ifs
  · rfl
  · exact congrFun₂ (right_complex L M p) _ _

theorem adjoined_family : Set.range (fun i : Fin (L.count+1) =>
    (⟨extendedArity L.count L.arity i.val,adjoined L M p i⟩ :
      AnySignature AlgebraicComplex)) =
      insert (⟨2,matrixSignature (right L M p)⟩ : AnySignature AlgebraicComplex) L.family := by
  exact (Holant.Complexity.EdgeSubdivision.extended_family
    (signatures L) (right L M p)).trans Set.union_singleton

theorem target_correct (r : SourceInput L) :
    (embedding L M p).toLinearMap
      (AlgebraicSource.CommonField.targetValue (complexFamily L) M.binary p r) =
        Problem.value .nativeX L ((inputIso L).symm r) := by
  apply SourceTransport.inclusion.injective
  change (AlgebraicSource.CommonField.targetValue (complexFamily L) M.binary p r : ℂ) = _
  rw [AlgebraicSource.CommonField.target_value_exact]
  have he := SourceTransport.closed_value (signatures L) r
  rw [← he]
  have hv := network_value .nativeX L ((inputIso L).symm r)
  exact congrArg SourceTransport.inclusion hv

theorem reduction (A : Language)
    (hA : A.family = insert
      (⟨2,matrixSignature (right L M p)⟩ : AnySignature AlgebraicComplex) L.family) :
    FixedFieldOutput.Reduces .nativeX A L := by
  have hs : A.family ⊆ Set.range (fun i : Fin (L.count+1) =>
      (⟨extendedArity L.count L.arity i.val,adjoined L M p i⟩ :
        AnySignature AlgebraicComplex)) := by
    rw [adjoined_family,hA]
  let q := FactorProvider.sourceInput (adjoined L M p) A hs
  have source_correct : ∀ r,
      (embedding L M p).toLinearMap
        (AlgebraicSource.CommonField.sourceValue (complexFamily L) M.binary p (q r)) =
          Problem.value .nativeX A r := by
    intro r
    apply SourceTransport.inclusion.injective
    change (AlgebraicSource.CommonField.sourceValue (complexFamily L) M.binary p (q r) : ℂ) = _
    rw [AlgebraicSource.CommonField.source_value_exact]
    rw [← adjoined_complex L M p,← SourceTransport.closed_value]
    exact congrArg SourceTransport.inclusion
      (FactorProvider.sourceDenote (adjoined L M p) A hs r)
  exact ⟨canonicalReduction .nativeX .nativeX A L
    (FieldSource.inputEncoding (s := L.count) (arity := L.arity))
    (presentation L M p) (embedding L M p).toLinearMap
    (AlgebraicSource.CommonField.sourceValue (complexFamily L) M.binary p)
    q (FactorProvider.sourceComputes (adjoined L M p) A hs) source_correct
    (presentation L M p) (embedding L M p).toLinearMap
    (embedding L M p).injective
    (AlgebraicSource.CommonField.targetValue (complexFamily L) M.binary p)
    (target_correct L M p)
    (BinaryQueryControl.controlled (complexFamily L) (complexAlgebraic L) M p)⟩

theorem infiniteOrder (B : Binary (K := AlgebraicComplex))
    (hmem : (⟨2,matrixSignature B⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hdet : Matrix.det (transfer B) ≠ 0) (hinf : ¬ ProjectivelyFinite (transfer B)) :
    ∃ (u v : Signature AlgebraicComplex 1) (A : Language), u ≠ 0 ∧ v ≠ 0 ∧
      A.family = insert (⟨2,Signature.tensor u v⟩ : AnySignature AlgebraicComplex) L.family ∧
      FixedFieldOutput.Reduces .nativeX A L := by
  have hB : B ≠ 0 := by
    intro hz
    simp [hz,transfer] at hdet
  have hreal : Holant.Gadget.Realizes L.family .disequality
      (Chains.binarySignature B) :=
    Holant.Gadget.realizes_of_mem _ _ _ hmem
  obtain ⟨M,p,_⟩ := SourceCapstone.binary_interpolation
    (complexFamily L) (complexAlgebraic L) (SourceTransport.binary B)
    (SourceTransport.binary_nonzero B hB)
    (SourceTransport.transfer_det_nonzero B hdet)
    (SourceTransport.transfer_infinite B hinf)
    (SourceTransport.realizes (signatures L) B hreal)
  obtain ⟨u,v,hu,hv,hf⟩ := singular_binary_factors
    (right L M p) (right_nonzero L M p) (right_singular L M p)
  let U : Signature AlgebraicComplex 1 := fun x => u (x 0)
  let V : Signature AlgebraicComplex 1 := fun x => v (x 0)
  have hU : U ≠ 0 := by
    intro h
    apply hu
    funext a
    exact congrFun h (fun _ => a)
  have hV : V ≠ 0 := by
    intro h
    apply hv
    funext a
    exact congrFun h (fun _ => a)
  have ht : matrixSignature (right L M p) = Signature.tensor U V := by
    funext x
    rw [matrixSignature,hf]
    rfl
  obtain ⟨A,hA⟩ := Language.coverage_family
    (insert (⟨2,Signature.tensor U V⟩ : AnySignature AlgebraicComplex) L.family)
    (L.family_finite.insert _)
  refine ⟨U,V,A,hU,hV,hA,?_⟩
  apply reduction L M p A
  simpa only [ht] using hA

end
end Paper2.Paper1Proved.InterpolationProvider

namespace Paper2.Paper1Proved
noncomputable section
theorem binaryInterpolationProvider : SourceFaithful.Paper1BinaryInterpolationAccepted where
  infiniteOrder_3_1 L _ _ B hmem hdet hinf :=
    InterpolationProvider.infiniteOrder L B hmem hdet hinf

end
end Paper2.Paper1Proved
