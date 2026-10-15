import Paper2.FixedFieldOutput.DropTag
import Paper2.FixedFieldOutput.BellPostprocessing
import Paper2.Complexity.BellMachines.RawClosuresCompile

/-! The three closure queries and their two circle flags, compiled from the
same actual exactly-two marked input. Every query is a validated original-L
instance, after literal label-shift removal of the discharged designation. -/
namespace Paper2.FixedFieldOutput.ClosureQueries
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines BellMachines
open Paper2.ExactInput Paper2.Problem Paper2.Tractable Paper2.RelativeEO
open BellPostprocessing
noncomputable section

abbrev Input (L : Language) (g : Signature AlgebraicComplex 2) := TaggedInstance L g (fun k => k = 2)

 def output (L : Language) (g : Signature AlgebraicComplex 2) (mode : Fin 3) (G : Input L g) :
    Instance L × (Bool × Bool) :=
  (BellReduction.RawClosures.query L g G.val G.property mode,
    (BellReduction.RawClosures.close mode G.val.val).firstCircle,
    (BellReduction.RawClosures.close mode G.val.val).secondCircle)

 def rawOutput (mode : Fin 3) (G : RawClosedNetwork) : RawClosedNetwork × (Bool × Bool) :=
  (DropTag.raw (RawClosures.close mode G).query,
    (RawClosures.close mode G).firstCircle,(RawClosures.close mode G).secondCircle)

 def rawComputes (mode : Fin 3) :
    Computes RawClosedNetwork.encoding (pairEncoding RawClosedNetwork.encoding pairBoolEncoding)
      (rawOutput mode) :=
  pairComputes (((RawClosures.computes mode).andThen RawClosures.queryComputes).andThen DropTag.rawComputes)
    ((RawClosures.computes mode).andThen RawClosures.flagsComputes)

 def computes (L : Language) (g : Signature AlgebraicComplex 2) (mode : Fin 3) :
    Computes (taggedEncoding L g (fun k => k = 2))
      (pairEncoding (inputEncoding L) pairBoolEncoding) (output L g mode) := by
  apply recode (rawComputes mode) (fun G => G.val.val) (fun _ => rfl)
  intro G
  have he := RawClosures.eq_close G.val.property (tagged_arity_zero L g)
    (show 2 ≤ BellReduction.RawOccurrence.markedCount G.val.val.vertices by exact G.property.ge) mode
  simp only [rawOutput,he,output,BellReduction.RawClosures.query]
  rfl

 def queryComputes (L : Language) (g : Signature AlgebraicComplex 2) (mode : Fin 3) :
    Computes (taggedEncoding L g (fun k => k = 2)) (inputEncoding L)
      (fun G => (output L g mode G).1) :=
  (computes L g mode).andThen (Wiring.firstComputes _ _)

 def flagsComputes (L : Language) (g : Signature AlgebraicComplex 2) (mode : Fin 3) :
    Computes (taggedEncoding L g (fun k => k = 2)) pairBoolEncoding
      (fun G => (output L g mode G).2) :=
  (computes L g mode).andThen (Wiring.secondComputes _ _)

 def allFlags (L : Language) (g : Signature AlgebraicComplex 2) (G : Input L g) : Flags :=
  ((output L g 0 G).2,(output L g 1 G).2,(output L g 2 G).2)

 def pre (L : Language) (g : Signature AlgebraicComplex 2) (G : Input L g) :
    Instance L × (Instance L × (Instance L × Flags)) :=
  ((output L g 0 G).1,(output L g 1 G).1,(output L g 2 G).1,allFlags L g G)

 def preComputes (L : Language) (g : Signature AlgebraicComplex 2) :
    Computes (taggedEncoding L g (fun k => k = 2))
      (UniversalPairReduction.ThreeQuery.contextEncoding (inputEncoding L) flagsEncoding) (pre L g) :=
  pairComputes (queryComputes L g 0) (pairComputes (queryComputes L g 1)
    (pairComputes (queryComputes L g 2)
      (pairComputes (flagsComputes L g 0) (pairComputes (flagsComputes L g 1) (flagsComputes L g 2)))))

end
end Paper2.FixedFieldOutput.ClosureQueries
