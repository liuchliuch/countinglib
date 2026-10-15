import Paper2.Paper1ProvedMarkedSubstitution

/-! Actual finite rational answer conversion for an exactly-one tagged oracle.
The promised graph compiler is supplied as a proved Computes value; the
controller derives clocks and valid query obligations for every prefix. -/
namespace Paper2.Paper1Proved
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.RelativeEO
open Paper2.Complexity BinaryCompose FixedFieldMachines FixedFieldOutput
open Paper2.Complexity.UniversalPairReduction.ThreeQuery
open Paper2.TractableAlgorithms.Paper1Machine
noncomputable section
set_option backward.isDefEq.respectTransparency false

def promisedFieldTargetReduction {A K : Type} [Field K] [Algebra ℚ K] {n r : ℕ}
    (L : Language) (g : Signature AlgebraicComplex r) (ea : Encoding A Bool)
    (F : Holant.Algebraic.FixedField K n) (embed : K →ₗ[ℚ] AlgebraicComplex)
    (injective : Function.Injective embed) (f : A → K)
    (q : A → TaggedInstance L g (fun k => k=1))
    (pre : Computes ea (taggedEncoding L g (fun k => k=1)) q)
    (correct : ∀ G,embed (f G)=Problem.value .nativeX (tagged L g) (q G).val) :
    LengthControlledOracleReduction ea F.encoding
      (taggedEncoding L g (fun k => k=1)) (answerEncoding (tagged L g))
      f (taggedAnswer .nativeX L g (fun k => k=1)) := by
  let pre3 := pairComputes pre (pairComputes pre
    (pairComputes pre (constantComputes ea encodingBoolBool false)))
  let first := Wiring.firstComputes (answerEncoding (tagged L g))
    (pairEncoding (answerEncoding (tagged L g))
      (pairEncoding (answerEncoding (tagged L g)) encodingBoolBool))
  let post := first.andThen (fieldConversionBack (tagged L g) F embed)
  exact controlledOfEq pre3 post (taggedOutputBound .nativeX L g (fun k => k=1)) f
    (fun G => (fieldConversionBack_correct (tagged L g) F embed injective .nativeX
      (q G).val (f G) (correct G)).symm)

def canonicalPromisedReduction {A B K : Type} [Field K] [Algebra ℚ K] {n r : ℕ}
    (source L : Language) (g : Signature AlgebraicComplex r)
    (ea : Encoding A Bool) (eb : Encoding B Bool)
    (F : Holant.Algebraic.FixedField K n) (embed : K →ₗ[ℚ] AlgebraicComplex)
    (injective : Function.Injective embed) (f : A → K) (target : B → K)
    (sourceInput : Instance source → A)
    (sourcePre : Computes (inputEncoding source) ea sourceInput)
    (sourceCorrect : ∀ G,embed (f (sourceInput G))=Problem.value .nativeX source G)
    (targetInput : B → TaggedInstance L g (fun k => k=1))
    (targetPre : Computes eb (taggedEncoding L g (fun k => k=1)) targetInput)
    (targetCorrect : ∀ G,embed (target G)=Problem.value .nativeX (tagged L g) (targetInput G).val)
    (old : Holant.Complexity.LengthControlledOracleReduction ea F.encoding eb F.encoding f target) :
    LengthControlledOracleReduction (inputEncoding source) (answerEncoding source)
      (taggedEncoding L g (fun k => k=1)) (answerEncoding (tagged L g))
      (answer .nativeX source) (taggedAnswer .nativeX L g (fun k => k=1)) :=
  (sourceFieldAdapter .nativeX source ea F embed f sourceInput sourcePre
    (controlledReduction old).sourceOutputBound sourceCorrect).controlledCompose
      ((controlledReduction old).controlledCompose
        (promisedFieldTargetReduction L g eb F embed injective target targetInput targetPre targetCorrect))

end
end Paper2.Paper1Proved
