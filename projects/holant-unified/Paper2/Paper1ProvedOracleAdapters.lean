import Paper2.Paper1ProvedRestrictionProvider

/-! Actual source and target adapters for the proved finite controlled source
programmes. They execute the graph compiler and fixed rational converters,
then inline every controlled oracle call with its actual byte certificate. -/
namespace Paper2.Paper1Proved
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.Complexity BinaryCompose FixedFieldMachines FixedFieldOutput
open Paper2.Complexity.UniversalPairReduction.ThreeQuery
open Paper2.TractableAlgorithms.Paper1Machine
open Holant.LocalDrafts.Hardness.GeneralExtraction
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev originalField (L : Language) := GeneralOriginalTarget.originalField (signatures L)
abbrev originalPresentation (L : Language) := GeneralOriginalTarget.originalPresentation (signatures L)
abbrev originalValue (L : Language) := GeneralOriginalTarget.originalValue (signatures L)
def originalEmbedding (L : Language) : originalField L →ₗ[ℚ] AlgebraicComplex :=
  (originalField L).val.toLinearMap

theorem originalEmbedding_correct (L : Language) (r : SourceInput L) :
    originalEmbedding L (originalValue L r) =
      Problem.value .nativeX L ((inputIso L).symm r) := by
  change (originalValue L r : AlgebraicComplex) = _
  rw [GeneralOriginalTarget.target_exact]
  have h := network_value .nativeX L ((inputIso L).symm r)
  change (((inputIso L) ((inputIso L).symm r)).val.realize
    (((inputIso L) ((inputIso L).symm r)).property) (signatures L) (kernels .nativeX)).denote Fin.elim0 = _ at h
  rw [Equiv.apply_symm_apply] at h
  rw [show Paper2.Paper1Proved.kernels .nativeX =
    (fun _ : Fin 1 => Holant.Signature.disequality) from rfl] at h
  exact h

def forwardFieldConversion {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (L : Language) (F : Holant.Algebraic.FixedField K n)
    (embed : K →ₗ[ℚ] AlgebraicComplex) :
    Computes F.encoding (answerEncoding L)
      (fun x => coordinates L (embed.comp F.decode.toLinearMap) (F.decode.symm x)) := by
  let vector : Computes F.encoding (Paper2.Algebraic.vectorEncoding n)
      (fun x => F.decode.symm x) :=
    recode (identityComputes F.encoding) id (fun _ => rfl)
      (fun x => vector_bytes_eq n (F.decode.symm x))
  exact vector.andThen (coordinatesComputes L (embed.comp F.decode.toLinearMap))

def sourceFieldAdapter {A K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (w : Wiring) (L : Language) (ea : Encoding A Bool)
    (F : Holant.Algebraic.FixedField K n) (embed : K →ₗ[ℚ] AlgebraicComplex)
    (f : A → K) (q : Instance L → A)
    (pre : Computes (inputEncoding L) ea q)
    (size : PolynomialOutputBound ea F.encoding f)
    (correct : ∀ G,embed (f (q G)) = Problem.value w L G) :
    LengthControlledOracleReduction (inputEncoding L) (answerEncoding L)
      ea F.encoding (answer w L) f := by
  let pre3 := pairComputes pre (pairComputes pre
    (pairComputes pre (constantComputes (inputEncoding L) encodingBoolBool false)))
  let first := Wiring.firstComputes F.encoding
    (pairEncoding F.encoding (pairEncoding F.encoding encodingBoolBool))
  let post := first.andThen (forwardFieldConversion L F embed)
  apply controlledOfEq pre3 post size (answer w L)
  intro G
  symm
  apply coordinates_correct L (embed.comp F.decode.toLinearMap) _ w G
  simpa only [answers,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using correct G

/-- Source graph compilation, source answer conversion, the original controlled
programme and the target answer conversion are all actual finite programmes. -/
def canonicalReduction {A K T : Type} [Field K] [Algebra ℚ K]
    [Field T] [Algebra ℚ T] {n m : ℕ}
    (ws wt : Wiring) (source target : Language) (ea : Encoding A Bool)
    (F : Holant.Algebraic.FixedField K n) (embed : K →ₗ[ℚ] AlgebraicComplex)
    (f : A → K) (q : Instance source → A)
    (pre : Computes (inputEncoding source) ea q)
    (sourceCorrect : ∀ G,embed (f (q G)) = Problem.value ws source G)
    (E : Holant.Algebraic.FixedField T m) (targetEmbed : T →ₗ[ℚ] AlgebraicComplex)
    (targetInjective : Function.Injective targetEmbed) (g : SourceInput target → T)
    (targetCorrect : ∀ G,targetEmbed (g G) = Problem.value wt target ((inputIso target).symm G))
    (r : Holant.Complexity.LengthControlledOracleReduction ea F.encoding
      (sourceEncoding target) E.encoding f g) :
    LengthControlledOracleReduction (inputEncoding source) (answerEncoding source)
      (inputEncoding target) (answerEncoding target) (answer ws source) (answer wt target) :=
  (sourceFieldAdapter ws source ea F embed f q pre
    (controlledReduction r).sourceOutputBound sourceCorrect).controlledCompose
      ((controlledReduction r).controlledCompose
        (fieldTargetReduction wt target E targetEmbed targetInjective g targetCorrect))

end
end Paper2.Paper1Proved
