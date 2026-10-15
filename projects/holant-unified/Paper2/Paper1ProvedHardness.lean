import Paper2.Paper1ProvedClassification
import Paper2.Paper1ProvedComplexity
import Paper2.TractableAlgorithms.Paper1Machine
import Paper2.FixedFieldOutput.Reductions

/-! Actual source-controlled Paper 1 hardness transported to the canonical
Paper 2 number-field answer. A real rational-matrix program converts answers;
the query program copies the identical validated graph bytes. All finite
programs, query validity, clocks and answer bounds occur in the proof. -/
namespace Paper2.Paper1Proved
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.Complexity BinaryCompose FixedFieldMachines
open Paper2.Complexity.UniversalPairReduction.ThreeQuery
open Paper2.TractableAlgorithms.Paper1Machine
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev SourceInput (L : Language) :=
  {r : Holant.Complexity.RawClosedNetwork // r.WellFormed L.count 1 L.arity}
abbrev sourceEncoding (L : Language) :=
  Holant.Complexity.RawClosedNetwork.validatedEncoding L.count 1 L.arity

/-- This is literally the identity word machine, with the original validation
record transported in its specification. -/
def queryComputes (L : Language) :
    Computes (sourceEncoding L) (inputEncoding L) (inputIso L).symm :=
  recode (identityComputes (sourceEncoding L)) id (fun _ => rfl) (input_bytes_back L)

def fieldTargetReduction {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (w : Wiring) (L : Language) (F : Holant.Algebraic.FixedField K n)
    (embed : K →ₗ[ℚ] AlgebraicComplex) (injective : Function.Injective embed)
    (f : SourceInput L → K)
    (correct : ∀ G,embed (f G) = Problem.value w L ((inputIso L).symm G)) :
    LengthControlledOracleReduction (sourceEncoding L) F.encoding
      (inputEncoding L) (FixedFieldOutput.answerEncoding L) f (FixedFieldOutput.answer w L) := by
  let pre := queryComputes L
  let pre3 := pairComputes pre (pairComputes pre
    (pairComputes pre (constantComputes (sourceEncoding L) encodingBoolBool false)))
  let first := Wiring.firstComputes (FixedFieldOutput.answerEncoding L)
    (pairEncoding (FixedFieldOutput.answerEncoding L)
      (pairEncoding (FixedFieldOutput.answerEncoding L) encodingBoolBool))
  let post := first.andThen (fieldConversionBack L F embed)
  exact controlledOfEq pre3 post (FixedFieldOutput.outputBound w L) f (fun G =>
    (fieldConversionBack_correct L F embed injective w ((inputIso L).symm G)
      (f G) (correct G)).symm)

/-- The counted verifier and all controlled source reductions are actual
proved Paper 1 data. No hardness callback beyond the source theorem is needed
when this generic transport is specialized below. -/
theorem canonicalFieldHard {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (w : Wiring) (L : Language) (F : Holant.Algebraic.FixedField K n)
    (embed : K →ₗ[ℚ] AlgebraicComplex) (injective : Function.Injective embed)
    (f : SourceInput L → K)
    (correct : ∀ G,embed (f G) = Problem.value w L ((inputIso L).symm G))
    (hard : ∀ (A : Type) (ea : Encoding A Bool) (count : A → ℕ),
      Holant.Complexity.SharpPWitness ea count →
        Nonempty (Holant.Complexity.LengthControlledOracleReduction ea
          encodingNatBool (sourceEncoding L) F.encoding count f)) :
    FixedFieldOutput.SharpPHard w L := by
  intro count hc
  obtain ⟨wc⟩ := hc
  obtain ⟨r⟩ := hard _ (encodingList Bool) count (sharpPWitness wc)
  exact ⟨(controlledReduction r).controlledCompose
    (fieldTargetReduction w L F embed injective f correct)⟩

abbrev nativeField (L : Language) :=
  Holant.Algebraic.familyField (OriginalFamily.coefficient (signatures L) (kernels .nativeX))

def nativeEmbedding (L : Language) : nativeField L →ₗ[ℚ] AlgebraicComplex :=
  (nativeField L).val.toLinearMap

theorem nativeEmbedding_correct (L : Language) (G : SourceInput L) :
    nativeEmbedding L (nativeValue L G) = Problem.value .nativeX L ((inputIso L).symm G) := by
  have h := Paper2.Paper1Proved.value .nativeX L ((inputIso L).symm G)
  change (nativeValue L ((inputIso L) ((inputIso L).symm G)) : AlgebraicComplex) = _ at h
  rwa [Equiv.apply_symm_apply] at h

theorem nativeControlledHard (L : Language)
    (hard : (PaperLiteralEqualityHardness.target (signatures L)).Hard) :
    FixedFieldOutput.SharpPHard .nativeX L :=
  canonicalFieldHard .nativeX L (nativePresentation L) (nativeEmbedding L)
    Subtype.val_injective (nativeValue L) (nativeEmbedding_correct L) hard

/-- Paper 1 Theorem 1.2 on the actual canonical field output of Paper 2. -/
theorem literalEqualityHard (L : Language) (h : HasLiteralEquality L)
    (hn : ¬ TractX (Paper2.kImage L)) : FixedFieldOutput.SharpPHard .nativeX L :=
  nativeControlledHard L (literalEqualityControlledHard L h hn)

/-- Paper 1 Theorem 1.3, preserving the complete original graph oracle. -/
theorem quaternaryHard (L : Language) (h : HasPrimeEightVertex L)
    (hn : ¬ Tract (Paper2.kImage L)) : FixedFieldOutput.SharpPHard .nativeX L :=
  nativeControlledHard L (quaternaryControlledHard L h hn)

end
end Paper2.Paper1Proved
