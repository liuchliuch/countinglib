import Paper2.FixedFieldOutput.ClosureQueries
import Paper2.BellReduction.OriginalQueries

/-! Genuine constant-query reductions for two designated Y or I occurrences.
The preprocessor, all three valid original-language queries, six circle flags,
canonical-field answer arithmetic and timing bounds are explicit checked code. -/
namespace Paper2.FixedFieldOutput.TwoBellReductions
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines
open Paper2.ExactInput Paper2.Problem Paper2.Tractable Paper2.RelativeEO
open UniversalPairReduction.ThreeQuery BellPostprocessing ClosureQueries
open Paper2.BellReduction
noncomputable section

 theorem factor_result (r : BellReduction.RawClosures.Result) :
    (pairFactor (r.firstCircle,r.secondCircle) : AlgebraicComplex) = BellReduction.RawClosures.scalar r := by
  cases h : r.firstCircle <;> cases h' : r.secondCircle <;>
    simp [pairFactor,flag,BellReduction.RawClosures.scalar,h,h']

 theorem flag_factor (L : Language) (g : Signature AlgebraicComplex 2) (G : Input L g) (i : Fin 3) :
    (pairFactor (readFlag i (allFlags L g G)) : AlgebraicComplex) =
      BellReduction.RawClosures.scalar (BellReduction.RawClosures.close i G.val.val) := by
  fin_cases i <;> exact factor_result _

 theorem post_query_value (L : Language) (g : Signature AlgebraicComplex 2)
    (coeff : Fin 3 → (tagged L g).coefficientField) (G : Input L g) :
    ((tagged L g).fieldPresentation.decode
      (post L (tagged L g) coeff (answers (answer .nativeX L) (pre L g G))) : AlgebraicComplex) =
    OriginalQueries.weightedQuery L g G.val G.property 0 * coeff 0 +
    OriginalQueries.weightedQuery L g G.val G.property 1 * coeff 1 +
    OriginalQueries.weightedQuery L g G.val G.property 2 * coeff 2 := by
  have hsub : L.family ⊆ (tagged L g).family := by
    rw [tagged_family]; exact Set.subset_insert _ _
  have h := post_correct L (tagged L g) hsub coeff
    (fun i => (output L g i G).1) (allFlags L g G)
  change ((tagged L g).fieldPresentation.decode
    (post L (tagged L g) coeff (answers (answer .nativeX L) (pre L g G))) : AlgebraicComplex) = _ at h
  rw [h,flag_factor,flag_factor,flag_factor]
  unfold OriginalQueries.weightedQuery output
  ring

 def twoY (L : Language) :
    LengthControlledOracleReduction
      (taggedEncoding L (bellTable true true) (fun k => k = 2))
      (answerEncoding (tagged L (bellTable true true)))
      (inputEncoding L) (answerEncoding L)
      (taggedAnswer .nativeX L (bellTable true true) (fun k => k = 2)) (answer .nativeX L) := by
  let g : Signature AlgebraicComplex 2 := bellTable true true
  apply controlledOfEq (preComputes L g) (BellPostprocessing.computes L (tagged L g)
    (twoYCoefficients (tagged L g))) (outputBound .nativeX L) _
  intro G
  symm
  apply answer_unique
  rw [post_query_value]
  have h := OriginalQueries.two_y L G.val G.property
  rw [h]
  change OriginalQueries.weightedQuery L g G.val G.property 0 * (0:AlgebraicComplex) +
    OriginalQueries.weightedQuery L g G.val G.property 1 * (-1:AlgebraicComplex) +
    OriginalQueries.weightedQuery L g G.val G.property 2 * (1:AlgebraicComplex) = _
  dsimp only [g]
  ring

 def twoI (L : Language) (hHigh : HighCharge L.family) :
    LengthControlledOracleReduction
      (taggedEncoding L (bellTable false false) (fun k => k = 2))
      (answerEncoding (tagged L (bellTable false false)))
      (inputEncoding L) (answerEncoding L)
      (taggedAnswer .nativeX L (bellTable false false) (fun k => k = 2)) (answer .nativeX L) := by
  let g : Signature AlgebraicComplex 2 := bellTable false false
  apply controlledOfEq (preComputes L g) (BellPostprocessing.computes L (tagged L g)
    (twoICoefficients (tagged L g))) (outputBound .nativeX L) _
  intro G
  symm
  apply answer_unique
  rw [post_query_value]
  have h := OriginalQueries.two_i L hHigh G.val G.property
  simp only [twoICoefficients,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  change OriginalQueries.weightedQuery L g G.val G.property 0 * (-(2:AlgebraicComplex)⁻¹) +
    OriginalQueries.weightedQuery L g G.val G.property 1 * (2:AlgebraicComplex)⁻¹ +
    OriginalQueries.weightedQuery L g G.val G.property 2 * (2:AlgebraicComplex)⁻¹ = _
  dsimp only [g] at *
  linear_combination -(1/2 : AlgebraicComplex) * h

 theorem twoY_reduces (L : Language) :
    TaggedReduces .nativeX L (bellTable true true) (fun k => k = 2) L := ⟨twoY L⟩
 theorem twoI_reduces (L : Language) (hHigh : HighCharge L.family) :
    TaggedReduces .nativeX L (bellTable false false) (fun k => k = 2) L := ⟨twoI L hHigh⟩

end
end Paper2.FixedFieldOutput.TwoBellReductions
