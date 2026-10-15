import Paper2.FixedFieldOutput.FieldTransport
import Paper2.Complexity.BellMachines.FixedPower
import Paper2.Complexity.BellMachines.UnaryRounds
import Paper2.Complexity.BellMachines.ThreeQuerySafe
import Paper2.BellReduction.Normalize

/-! Original graph bytes to an actual at-most-two-occurrence oracle. The finite
preprocessor normalizes the graph and scans the original occurrence counter;
the finite postprocessor divides by the exact fixed scalar power. All query
and answer lengths are charged by the checked multi-query controller. -/
namespace Paper2.FixedFieldOutput
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines BellMachines
open GraphPreprocessing UniversalPairReduction.ThreeQuery
open Paper2.ExactInput Paper2.Problem Paper2.Tractable Paper2.BellReduction
noncomputable section

abbrev ResidualInstance (L : Language) :=
  {G : Instance L // RawOccurrence.markedCount G.val.vertices ≤ 2}

def residualEncoding (L : Language) : Encoding (ResidualInstance L) Bool where
  encode G := (inputEncoding L).encode G.val
  decode bits := ((inputEncoding L).decode bits).bind
    (fun G => if h : RawOccurrence.markedCount G.val.vertices ≤ 2 then some ⟨G,h⟩ else none)
  decode_encode G := by simp [G.property]

 def residualAnswer (L : Language) (G : ResidualInstance L) : Answer L := answer .nativeX L G.val

 def residualOutputBound (L : Language) :
    PolynomialOutputBound (residualEncoding L) (answerEncoding L) (residualAnswer L) where
  bound := (outputBound .nativeX L).bound
  length_le G := (outputBound .nativeX L).length_le G.val

 def roundsComputes (L : Language) : Computes (inputEncoding L) UnaryBinary.unaryEncoding
    (fun G => roundsRemaining G) :=
  recode UnaryRounds.graphComputes Subtype.val (fun _ => rfl) (fun _ => rfl)

 def normalizedQuery (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (G : Instance L) : ResidualInstance L :=
  ⟨normalize L hzero coreLabel hl ha G,normalize_count L hzero coreLabel hl ha G⟩

 def normalizedQueryComputes (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8) :
    Computes (inputEncoding L) (residualEncoding L) (normalizedQuery L hzero coreLabel hl ha) :=
  recode (normalizeComputes L hzero coreLabel hl ha) id (fun _ => rfl) (fun _ => rfl)

 def decodeComputes (L : Language) :
    Computes (answerEncoding L) L.fieldPresentation.encoding L.fieldPresentation.decode :=
  recode (identityComputes (answerEncoding L)) id (fun _ => rfl)
    (fun v => (L.fieldPresentation.encoding_decode v).symm)

 def correction (L : Language) (s : L.coefficientField)
    (p : Answer L × (Answer L × (Answer L × ℕ))) : Answer L :=
  L.fieldPresentation.basis.equivFun (L.fieldPresentation.decode p.1 / s^p.2.2.2)

 def correctionComputes (L : Language) (s : L.coefficientField) :
    Computes (contextEncoding (answerEncoding L) UnaryBinary.unaryEncoding)
      (answerEncoding L) (correction L s) := by
  let value := (Wiring.firstComputes (answerEncoding L)
    (pairEncoding (answerEncoding L) (pairEncoding (answerEncoding L) UnaryBinary.unaryEncoding))).andThen
      (decodeComputes L)
  let count := ((Wiring.secondComputes (answerEncoding L)
    (pairEncoding (answerEncoding L) (pairEncoding (answerEncoding L) UnaryBinary.unaryEncoding))).andThen
      (Wiring.secondComputes (answerEncoding L) (pairEncoding (answerEncoding L) UnaryBinary.unaryEncoding))).andThen
        (Wiring.secondComputes (answerEncoding L) UnaryBinary.unaryEncoding)
  exact ((pairComputes count value).andThen (correctByPowerComputes L.fieldPresentation s)).andThen
    (fromFieldComputes L)

 theorem core_scalar_mem (L : Language) (coreLabel : ℕ) (hl : coreLabel < L.count)
    (c : AlgebraicComplex)
    (hcore : (⟨L.arity coreLabel,L.signature ⟨coreLabel,hl⟩⟩ : AnySignature AlgebraicComplex) =
      ⟨8,fun x => c * ReedMuller.core x⟩) : c ∈ L.coefficientField := by
  have h := congrArg (fun g : AnySignature AlgebraicComplex => g.2 (fun _ => false)) hcore
  have hz : ReedMuller.IsCodeword (fun _ => false) :=
    ⟨fun _ => false,by funext i; simp [ReedMuller.affineWord]⟩
  have he : L.signature ⟨coreLabel,hl⟩ (fun _ => false) = c := by
    simpa [ReedMuller.core,hz] using h
  exact he ▸ L.signature_mem_field ⟨coreLabel,hl⟩ (fun _ => false)

 def fieldScale (L : Language) (coreLabel : ℕ) (hl : coreLabel < L.count)
    (c : AlgebraicComplex)
    (hcore : (⟨L.arity coreLabel,L.signature ⟨coreLabel,hl⟩⟩ : AnySignature AlgebraicComplex) =
      ⟨8,fun x => c * ReedMuller.core x⟩) (l : Bool) : L.coefficientField :=
  ⟨c,core_scalar_mem L coreLabel hl c hcore⟩ * Bell.sign l

 theorem fieldScale_coe (L : Language) (coreLabel : ℕ) (hl : coreLabel < L.count)
    (c : AlgebraicComplex)
    (hcore : (⟨L.arity coreLabel,L.signature ⟨coreLabel,hl⟩⟩ : AnySignature AlgebraicComplex) =
      ⟨8,fun x => c * ReedMuller.core x⟩) (l : Bool) :
    (fieldScale L coreLabel hl c hcore l : AlgebraicComplex) = c * Bell.sign l := by
  cases l <;> simp [fieldScale,Bell.sign]

 def normalizationReduction (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (c : AlgebraicComplex) (hc : c ≠ 0) (d l : Bool) (hL0 : 0 < L.count)
    (hbell : (⟨L.arity 0,L.signature ⟨0,hL0⟩⟩ : AnySignature AlgebraicComplex) =
      ⟨2,bellTable d l⟩)
    (hcore : (⟨L.arity coreLabel,L.signature ⟨coreLabel,hl⟩⟩ : AnySignature AlgebraicComplex) =
      ⟨8,fun x => c * ReedMuller.core x⟩) :
    LengthControlledOracleReduction (inputEncoding L) (answerEncoding L)
      (residualEncoding L) (answerEncoding L) (answer .nativeX L) (residualAnswer L) := by
  let query := normalizedQueryComputes L hzero coreLabel hl ha
  let pre := pairComputes query (pairComputes query (pairComputes query (roundsComputes L)))
  let s := fieldScale L coreLabel hl c hcore l
  apply controlledOfEq pre (correctionComputes L s) (residualOutputBound L) (answer .nativeX L)
  intro G
  symm
  apply answer_unique
  change (L.fieldPresentation.decode (L.fieldPresentation.basis.equivFun
    (L.fieldPresentation.decode (answer .nativeX L (normalize L hzero coreLabel hl ha G)) /
      s^roundsRemaining G)) : AlgebraicComplex) = _
  rw [show L.fieldPresentation.decode (L.fieldPresentation.basis.equivFun
      (L.fieldPresentation.decode (answer .nativeX L (normalize L hzero coreLabel hl ha G)) /
        s^roundsRemaining G)) =
      L.fieldPresentation.decode (answer .nativeX L (normalize L hzero coreLabel hl ha G)) /
        s^roundsRemaining G from L.fieldPresentation.basis.equivFun.symm_apply_apply _]
  change L.coefficientField.val (_ / _) = _
  rw [map_div₀,map_pow]
  change (L.fieldPresentation.decode (answer .nativeX L (normalize L hzero coreLabel hl ha G)) : AlgebraicComplex) /
    (s : AlgebraicComplex)^roundsRemaining G = _
  rw [answer_correct,fieldScale_coe]
  exact (original_value_from_normalized L hzero coreLabel hl ha c d l hL0 hbell hcore hc G).symm

end
end Paper2.FixedFieldOutput
